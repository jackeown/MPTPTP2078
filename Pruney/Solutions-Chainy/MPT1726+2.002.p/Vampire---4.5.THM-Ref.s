%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:08 EST 2020

% Result     : Theorem 3.92s
% Output     : Refutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  920 (3437 expanded)
%              Number of leaves         :  261 (1767 expanded)
%              Depth                    :    9
%              Number of atoms          : 8737 (28089 expanded)
%              Number of equality atoms :    4 ( 152 expanded)
%              Maximal formula depth    :   24 (  12 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f184,f189,f191,f206,f222,f226,f230,f232,f237,f238,f240,f247,f251,f267,f271,f275,f281,f303,f310,f335,f339,f343,f355,f371,f375,f379,f394,f399,f408,f412,f416,f431,f435,f440,f450,f454,f458,f468,f472,f476,f486,f490,f494,f518,f522,f526,f548,f552,f556,f566,f570,f574,f589,f596,f607,f611,f615,f620,f646,f650,f654,f670,f674,f678,f679,f680,f696,f700,f704,f747,f751,f755,f783,f787,f791,f805,f809,f813,f823,f839,f843,f847,f869,f873,f877,f895,f912,f927,f939,f943,f947,f961,f965,f966,f970,f974,f978,f1021,f1025,f1029,f1041,f1053,f1057,f1061,f1065,f1131,f1135,f1139,f1155,f1159,f1163,f1164,f1165,f1166,f1167,f1195,f1199,f1203,f1233,f1264,f1268,f1297,f1301,f1305,f1325,f1329,f1333,f1337,f1348,f1393,f1397,f1401,f1414,f1418,f1422,f1447,f1451,f1455,f1473,f1477,f1481,f1494,f1498,f1502,f1533,f1537,f1541,f1553,f1558,f1576,f1580,f1584,f1596,f1600,f1604,f1608,f1626,f1635,f1636,f1645,f1649,f1653,f1657,f1694,f1698,f1702,f1715,f1719,f1723,f1736,f1740,f1744,f1758,f1772,f1776,f1780,f1794,f1798,f1802,f1806,f1810,f1824,f1828,f1832,f1845,f1855,f1859,f1863,f1876,f1880,f1884,f1910,f1914,f1918,f1922,f1931,f1940,f1941,f1945,f1949,f1953,f1957,f1998,f2002,f2006,f2010,f2011,f2015,f2019,f2023,f2027,f2055,f2059,f2063,f2077,f2081,f2085,f2099,f2103,f2107,f2120,f2124,f2128,f2154,f2158,f2162,f2163,f2167,f2171,f2175,f2179])).

fof(f2179,plain,
    ( spl5_18
    | spl5_248
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2142,f867,f2177,f174])).

fof(f174,plain,
    ( spl5_18
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f2177,plain,
    ( spl5_248
  <=> ! [X18,X17,X19] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | ~ m1_pre_topc(k2_tsep_1(X19,X17,X18),sK0)
        | v2_struct_0(k2_tsep_1(X19,X17,X18))
        | ~ m1_pre_topc(k2_tsep_1(X19,X17,X18),sK1)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X19)
        | r1_tsep_1(X18,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X18,X19) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_248])])).

fof(f867,plain,
    ( spl5_106
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f2142,plain,
    ( ! [X19,X17,X18] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | r1_tsep_1(X18,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X17,X19)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(k2_tsep_1(X19,X17,X18),sK1)
        | v2_struct_0(k2_tsep_1(X19,X17,X18))
        | ~ m1_pre_topc(k2_tsep_1(X19,X17,X18),sK0) )
    | ~ spl5_106 ),
    inference(resolution,[],[f57,f868])).

fof(f868,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f867])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).

fof(f2175,plain,
    ( spl5_18
    | spl5_247
    | ~ spl5_153 ),
    inference(avatar_split_clause,[],[f2141,f1445,f2173,f174])).

fof(f2173,plain,
    ( spl5_247
  <=> ! [X16,X15,X14] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14)
        | ~ m1_pre_topc(k2_tsep_1(X16,X14,X15),sK0)
        | v2_struct_0(k2_tsep_1(X16,X14,X15))
        | ~ m1_pre_topc(k2_tsep_1(X16,X14,X15),sK3)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X16)
        | r1_tsep_1(X15,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X15,X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_247])])).

fof(f1445,plain,
    ( spl5_153
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f2141,plain,
    ( ! [X14,X15,X16] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14)
        | r1_tsep_1(X15,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X14,X16)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X15,X16)
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(k2_tsep_1(X16,X14,X15),sK3)
        | v2_struct_0(k2_tsep_1(X16,X14,X15))
        | ~ m1_pre_topc(k2_tsep_1(X16,X14,X15),sK0) )
    | ~ spl5_153 ),
    inference(resolution,[],[f57,f1446])).

fof(f1446,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_153 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f2171,plain,
    ( spl5_18
    | spl5_246
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f2140,f1574,f2169,f174])).

fof(f2169,plain,
    ( spl5_246
  <=> ! [X11,X13,X10,X12] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(k2_tsep_1(X12,X10,X11),sK0)
        | ~ m1_pre_topc(X13,sK1)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(k2_tsep_1(X12,X10,X11))
        | ~ m1_pre_topc(k2_tsep_1(X12,X10,X11),X13)
        | v2_struct_0(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X12)
        | r1_tsep_1(X11,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_246])])).

fof(f1574,plain,
    ( spl5_167
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f2140,plain,
    ( ! [X12,X10,X13,X11] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | r1_tsep_1(X11,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X10,X12)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,X12)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(k2_tsep_1(X12,X10,X11),X13)
        | v2_struct_0(k2_tsep_1(X12,X10,X11))
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X13,sK1)
        | ~ m1_pre_topc(k2_tsep_1(X12,X10,X11),sK0) )
    | ~ spl5_167 ),
    inference(resolution,[],[f57,f1575])).

fof(f1575,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_167 ),
    inference(avatar_component_clause,[],[f1574])).

fof(f2167,plain,
    ( spl5_18
    | spl5_245
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2139,f1822,f2165,f174])).

fof(f2165,plain,
    ( spl5_245
  <=> ! [X9,X7,X8,X6] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(k2_tsep_1(X8,X6,X7),sK0)
        | ~ m1_pre_topc(X9,sK3)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(k2_tsep_1(X8,X6,X7))
        | ~ m1_pre_topc(k2_tsep_1(X8,X6,X7),X9)
        | v2_struct_0(X9)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X8)
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_245])])).

fof(f1822,plain,
    ( spl5_200
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f2139,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(X8,X6,X7),X9)
        | v2_struct_0(k2_tsep_1(X8,X6,X7))
        | ~ m1_pre_topc(X9,sK0)
        | ~ m1_pre_topc(X9,sK3)
        | ~ m1_pre_topc(k2_tsep_1(X8,X6,X7),sK0) )
    | ~ spl5_200 ),
    inference(resolution,[],[f57,f1823])).

fof(f1823,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_200 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f2163,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_8
    | ~ spl5_7
    | spl5_14
    | ~ spl5_13
    | spl5_12
    | ~ spl5_11
    | spl5_2
    | ~ spl5_6
    | ~ spl5_165 ),
    inference(avatar_split_clause,[],[f2137,f1550,f93,f74,f118,f123,f128,f133,f98,f103,f138,f143,f148])).

fof(f148,plain,
    ( spl5_17
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f143,plain,
    ( spl5_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f138,plain,
    ( spl5_15
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f103,plain,
    ( spl5_8
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f98,plain,
    ( spl5_7
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f133,plain,
    ( spl5_14
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f128,plain,
    ( spl5_13
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f123,plain,
    ( spl5_12
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f118,plain,
    ( spl5_11
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f74,plain,
    ( spl5_2
  <=> r1_tsep_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f93,plain,
    ( spl5_6
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1550,plain,
    ( spl5_165
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f2137,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_165 ),
    inference(resolution,[],[f57,f1552])).

fof(f1552,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | ~ spl5_165 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f2162,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_244
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f2148,f1193,f2160,f118,f123,f98,f103,f138,f143,f148])).

fof(f2160,plain,
    ( spl5_244
  <=> ! [X4] :
        ( ~ m1_pre_topc(X4,sK2)
        | ~ m1_pre_topc(X4,sK3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | r1_tsep_1(sK4,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_244])])).

fof(f1193,plain,
    ( spl5_134
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f2148,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK2)
        | r1_tsep_1(sK4,X4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X4,sK3) )
    | ~ spl5_134 ),
    inference(duplicate_literal_removal,[],[f2134])).

fof(f2134,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK2)
        | r1_tsep_1(sK4,X4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X4,sK3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0) )
    | ~ spl5_134 ),
    inference(resolution,[],[f57,f1194])).

fof(f1194,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_134 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f2158,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_243
    | ~ spl5_188 ),
    inference(avatar_split_clause,[],[f2149,f1734,f2156,f118,f123,f98,f103,f138,f143,f148])).

fof(f2156,plain,
    ( spl5_243
  <=> ! [X3,X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(sK4,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_243])])).

fof(f1734,plain,
    ( spl5_188
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f2149,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK2)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl5_188 ),
    inference(duplicate_literal_removal,[],[f2133])).

fof(f2133,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK2)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl5_188 ),
    inference(resolution,[],[f57,f1735])).

fof(f1735,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl5_188 ),
    inference(avatar_component_clause,[],[f1734])).

fof(f2154,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_242
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f2150,f1770,f2152,f118,f123,f98,f103,f138,f143,f148])).

fof(f2152,plain,
    ( spl5_242
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_242])])).

fof(f1770,plain,
    ( spl5_192
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f2150,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl5_192 ),
    inference(duplicate_literal_removal,[],[f2132])).

fof(f2132,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_192 ),
    inference(resolution,[],[f57,f1771])).

fof(f1771,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_192 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f2128,plain,
    ( spl5_10
    | spl5_241
    | ~ spl5_127 ),
    inference(avatar_split_clause,[],[f2115,f1063,f2126,f113])).

fof(f113,plain,
    ( spl5_10
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f2126,plain,
    ( spl5_241
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X8,sK3)
        | r1_tsep_1(X8,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_241])])).

fof(f1063,plain,
    ( spl5_127
  <=> ! [X7,X6] :
        ( r1_tsep_1(X6,sK2)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X7)
        | ~ m1_pre_topc(sK2,X7)
        | ~ m1_pre_topc(sK3,X7)
        | ~ m1_pre_topc(X6,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f2115,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(X8,sK2)
        | ~ m1_pre_topc(X8,sK3)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_127 ),
    inference(resolution,[],[f1064,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f50,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f1064,plain,
    ( ! [X6,X7] :
        ( ~ m1_pre_topc(sK3,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X7)
        | ~ m1_pre_topc(sK2,X7)
        | r1_tsep_1(X6,sK2)
        | ~ m1_pre_topc(X6,sK3) )
    | ~ spl5_127 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f2124,plain,
    ( spl5_10
    | spl5_240
    | ~ spl5_127 ),
    inference(avatar_split_clause,[],[f2114,f1063,f2122,f113])).

fof(f2122,plain,
    ( spl5_240
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X5,sK3)
        | r1_tsep_1(X5,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_240])])).

fof(f2114,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(X5,sK2)
        | ~ m1_pre_topc(X5,sK3)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_127 ),
    inference(resolution,[],[f1064,f50])).

fof(f2120,plain,
    ( ~ spl5_11
    | spl5_239
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_9
    | ~ spl5_127 ),
    inference(avatar_split_clause,[],[f2112,f1063,f108,f148,f143,f138,f2118,f118])).

fof(f2118,plain,
    ( spl5_239
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_239])])).

fof(f108,plain,
    ( spl5_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f2112,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl5_9
    | ~ spl5_127 ),
    inference(resolution,[],[f1064,f110])).

fof(f110,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f2107,plain,
    ( spl5_10
    | spl5_238
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f2094,f1059,f2105,f113])).

fof(f2105,plain,
    ( spl5_238
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X8,sK3)
        | r1_tsep_1(sK2,X8)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_238])])).

fof(f1059,plain,
    ( spl5_126
  <=> ! [X5,X4] :
        ( r1_tsep_1(sK2,X4)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(sK2,X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ m1_pre_topc(X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f2094,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(sK2,X8)
        | ~ m1_pre_topc(X8,sK3)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_126 ),
    inference(resolution,[],[f1060,f167])).

fof(f1060,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(sK2,X5)
        | r1_tsep_1(sK2,X4)
        | ~ m1_pre_topc(X4,sK3) )
    | ~ spl5_126 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f2103,plain,
    ( spl5_10
    | spl5_237
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f2093,f1059,f2101,f113])).

fof(f2101,plain,
    ( spl5_237
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X5,sK3)
        | r1_tsep_1(sK2,X5)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).

fof(f2093,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(sK2,X5)
        | ~ m1_pre_topc(X5,sK3)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_126 ),
    inference(resolution,[],[f1060,f50])).

fof(f2099,plain,
    ( ~ spl5_11
    | spl5_236
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_9
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f2091,f1059,f108,f148,f143,f138,f2097,f118])).

fof(f2097,plain,
    ( spl5_236
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_236])])).

fof(f2091,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl5_9
    | ~ spl5_126 ),
    inference(resolution,[],[f1060,f110])).

fof(f2085,plain,
    ( spl5_10
    | spl5_235
    | ~ spl5_125 ),
    inference(avatar_split_clause,[],[f2072,f1055,f2083,f113])).

fof(f2083,plain,
    ( spl5_235
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X8,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(X8,sK3)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_235])])).

fof(f1055,plain,
    ( spl5_125
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,sK3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(sK2,X3)
        | ~ m1_pre_topc(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f2072,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(X8,sK3)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(X8,sK2)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_125 ),
    inference(resolution,[],[f1056,f167])).

fof(f1056,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | r1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(sK2,X3)
        | ~ m1_pre_topc(X2,sK2) )
    | ~ spl5_125 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f2081,plain,
    ( spl5_10
    | spl5_234
    | ~ spl5_125 ),
    inference(avatar_split_clause,[],[f2071,f1055,f2079,f113])).

fof(f2079,plain,
    ( spl5_234
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X5,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(X5,sK3)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_234])])).

fof(f2071,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(X5,sK3)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(X5,sK2)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_125 ),
    inference(resolution,[],[f1056,f50])).

fof(f2077,plain,
    ( ~ spl5_11
    | spl5_233
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_9
    | ~ spl5_125 ),
    inference(avatar_split_clause,[],[f2069,f1055,f108,f148,f143,f138,f2075,f118])).

fof(f2075,plain,
    ( spl5_233
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_233])])).

fof(f2069,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK2) )
    | ~ spl5_9
    | ~ spl5_125 ),
    inference(resolution,[],[f1056,f110])).

fof(f2063,plain,
    ( spl5_10
    | spl5_232
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f2050,f1051,f2061,f113])).

fof(f2061,plain,
    ( spl5_232
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X8,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(sK3,X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).

fof(f1051,plain,
    ( spl5_124
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK3,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f2050,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(sK3,X8)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(X8,sK2)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_124 ),
    inference(resolution,[],[f1052,f167])).

fof(f1052,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f2059,plain,
    ( spl5_10
    | spl5_231
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f2049,f1051,f2057,f113])).

fof(f2057,plain,
    ( spl5_231
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X5,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(sK3,X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_231])])).

fof(f2049,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(sK3,X5)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(X5,sK2)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_124 ),
    inference(resolution,[],[f1052,f50])).

fof(f2055,plain,
    ( ~ spl5_11
    | spl5_230
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_9
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f2047,f1051,f108,f148,f143,f138,f2053,f118])).

fof(f2053,plain,
    ( spl5_230
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tsep_1(sK3,X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_230])])).

fof(f2047,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(sK3,X1)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK2) )
    | ~ spl5_9
    | ~ spl5_124 ),
    inference(resolution,[],[f1052,f110])).

fof(f2027,plain,
    ( spl5_18
    | spl5_229
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f1986,f867,f2025,f174])).

fof(f2025,plain,
    ( spl5_229
  <=> ! [X18,X17,X19] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | ~ m1_pre_topc(k2_tsep_1(X19,X18,X17),sK0)
        | v2_struct_0(k2_tsep_1(X19,X18,X17))
        | ~ m1_pre_topc(k2_tsep_1(X19,X18,X17),sK1)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X19)
        | r1_tsep_1(X18,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X18,X19) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_229])])).

fof(f1986,plain,
    ( ! [X19,X17,X18] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | r1_tsep_1(X18,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X17,X19)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(k2_tsep_1(X19,X18,X17),sK1)
        | v2_struct_0(k2_tsep_1(X19,X18,X17))
        | ~ m1_pre_topc(k2_tsep_1(X19,X18,X17),sK0) )
    | ~ spl5_106 ),
    inference(resolution,[],[f56,f868])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2023,plain,
    ( spl5_18
    | spl5_228
    | ~ spl5_153 ),
    inference(avatar_split_clause,[],[f1985,f1445,f2021,f174])).

fof(f2021,plain,
    ( spl5_228
  <=> ! [X16,X15,X14] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14)
        | ~ m1_pre_topc(k2_tsep_1(X16,X15,X14),sK0)
        | v2_struct_0(k2_tsep_1(X16,X15,X14))
        | ~ m1_pre_topc(k2_tsep_1(X16,X15,X14),sK3)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X16)
        | r1_tsep_1(X15,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X15,X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_228])])).

fof(f1985,plain,
    ( ! [X14,X15,X16] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14)
        | r1_tsep_1(X15,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X14,X16)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X15,X16)
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(k2_tsep_1(X16,X15,X14),sK3)
        | v2_struct_0(k2_tsep_1(X16,X15,X14))
        | ~ m1_pre_topc(k2_tsep_1(X16,X15,X14),sK0) )
    | ~ spl5_153 ),
    inference(resolution,[],[f56,f1446])).

fof(f2019,plain,
    ( spl5_18
    | spl5_227
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1984,f1574,f2017,f174])).

fof(f2017,plain,
    ( spl5_227
  <=> ! [X11,X13,X10,X12] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(k2_tsep_1(X12,X11,X10),sK0)
        | ~ m1_pre_topc(X13,sK1)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(k2_tsep_1(X12,X11,X10))
        | ~ m1_pre_topc(k2_tsep_1(X12,X11,X10),X13)
        | v2_struct_0(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X12)
        | r1_tsep_1(X11,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_227])])).

fof(f1984,plain,
    ( ! [X12,X10,X13,X11] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | r1_tsep_1(X11,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X10,X12)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,X12)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(k2_tsep_1(X12,X11,X10),X13)
        | v2_struct_0(k2_tsep_1(X12,X11,X10))
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X13,sK1)
        | ~ m1_pre_topc(k2_tsep_1(X12,X11,X10),sK0) )
    | ~ spl5_167 ),
    inference(resolution,[],[f56,f1575])).

fof(f2015,plain,
    ( spl5_18
    | spl5_226
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f1983,f1822,f2013,f174])).

fof(f2013,plain,
    ( spl5_226
  <=> ! [X9,X7,X8,X6] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(k2_tsep_1(X8,X7,X6),sK0)
        | ~ m1_pre_topc(X9,sK3)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(k2_tsep_1(X8,X7,X6))
        | ~ m1_pre_topc(k2_tsep_1(X8,X7,X6),X9)
        | v2_struct_0(X9)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X8)
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_226])])).

fof(f1983,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(X8,X7,X6),X9)
        | v2_struct_0(k2_tsep_1(X8,X7,X6))
        | ~ m1_pre_topc(X9,sK0)
        | ~ m1_pre_topc(X9,sK3)
        | ~ m1_pre_topc(k2_tsep_1(X8,X7,X6),sK0) )
    | ~ spl5_200 ),
    inference(resolution,[],[f56,f1823])).

fof(f2011,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_10
    | ~ spl5_9
    | spl5_8
    | ~ spl5_7
    | spl5_1
    | ~ spl5_5
    | ~ spl5_166 ),
    inference(avatar_split_clause,[],[f1982,f1555,f88,f70,f98,f103,f108,f113,f118,f123,f138,f143,f148])).

fof(f70,plain,
    ( spl5_1
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f88,plain,
    ( spl5_5
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1555,plain,
    ( spl5_166
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f1982,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_166 ),
    inference(resolution,[],[f56,f1557])).

fof(f1557,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | ~ spl5_166 ),
    inference(avatar_component_clause,[],[f1555])).

fof(f2010,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_225
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f1991,f644,f2008,f98,f103,f118,f123,f138,f143,f148])).

fof(f2008,plain,
    ( spl5_225
  <=> ! [X5] :
        ( ~ m1_pre_topc(X5,sK4)
        | ~ m1_pre_topc(X5,sK1)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | r1_tsep_1(sK2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_225])])).

fof(f644,plain,
    ( spl5_81
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f1991,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK4)
        | r1_tsep_1(sK2,X5)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X5,sK1) )
    | ~ spl5_81 ),
    inference(duplicate_literal_removal,[],[f1979])).

fof(f1979,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK4)
        | r1_tsep_1(sK2,X5)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X5,sK1)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0) )
    | ~ spl5_81 ),
    inference(resolution,[],[f56,f645])).

fof(f645,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f644])).

fof(f2006,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_224
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f1992,f1193,f2004,f98,f103,f118,f123,f138,f143,f148])).

fof(f2004,plain,
    ( spl5_224
  <=> ! [X4] :
        ( ~ m1_pre_topc(X4,sK4)
        | ~ m1_pre_topc(X4,sK3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | r1_tsep_1(sK2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).

fof(f1992,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK4)
        | r1_tsep_1(sK2,X4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X4,sK3) )
    | ~ spl5_134 ),
    inference(duplicate_literal_removal,[],[f1978])).

fof(f1978,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK4)
        | r1_tsep_1(sK2,X4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X4,sK3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0) )
    | ~ spl5_134 ),
    inference(resolution,[],[f56,f1194])).

fof(f2002,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_223
    | ~ spl5_188 ),
    inference(avatar_split_clause,[],[f1993,f1734,f2000,f98,f103,f118,f123,f138,f143,f148])).

fof(f2000,plain,
    ( spl5_223
  <=> ! [X3,X2] :
        ( ~ m1_pre_topc(X2,sK4)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).

fof(f1993,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK4)
        | r1_tsep_1(sK2,X2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl5_188 ),
    inference(duplicate_literal_removal,[],[f1977])).

fof(f1977,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK4)
        | r1_tsep_1(sK2,X2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl5_188 ),
    inference(resolution,[],[f56,f1735])).

fof(f1998,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_222
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1994,f1770,f1996,f98,f103,f118,f123,f138,f143,f148])).

fof(f1996,plain,
    ( spl5_222
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).

fof(f1994,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl5_192 ),
    inference(duplicate_literal_removal,[],[f1976])).

fof(f1976,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_192 ),
    inference(resolution,[],[f56,f1771])).

fof(f1957,plain,
    ( spl5_18
    | spl5_221
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f1898,f867,f1955,f174])).

fof(f1955,plain,
    ( spl5_221
  <=> ! [X18,X17,X19] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | ~ m1_pre_topc(k2_tsep_1(X19,X18,X17),sK0)
        | v2_struct_0(k2_tsep_1(X19,X18,X17))
        | ~ m1_pre_topc(k2_tsep_1(X19,X18,X17),sK1)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19)
        | v2_struct_0(X18)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X19)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X18)
        | ~ m1_pre_topc(X18,X19) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_221])])).

fof(f1898,plain,
    ( ! [X19,X17,X18] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X18)
        | ~ m1_pre_topc(X17,X19)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(k2_tsep_1(X19,X18,X17),sK1)
        | v2_struct_0(k2_tsep_1(X19,X18,X17))
        | ~ m1_pre_topc(k2_tsep_1(X19,X18,X17),sK0) )
    | ~ spl5_106 ),
    inference(resolution,[],[f55,f868])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1953,plain,
    ( spl5_18
    | spl5_220
    | ~ spl5_153 ),
    inference(avatar_split_clause,[],[f1897,f1445,f1951,f174])).

fof(f1951,plain,
    ( spl5_220
  <=> ! [X16,X15,X14] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14)
        | ~ m1_pre_topc(k2_tsep_1(X16,X15,X14),sK0)
        | v2_struct_0(k2_tsep_1(X16,X15,X14))
        | ~ m1_pre_topc(k2_tsep_1(X16,X15,X14),sK3)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16)
        | v2_struct_0(X15)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X16)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X15)
        | ~ m1_pre_topc(X15,X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_220])])).

fof(f1897,plain,
    ( ! [X14,X15,X16] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X15)
        | ~ m1_pre_topc(X14,X16)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X15,X16)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(k2_tsep_1(X16,X15,X14),sK3)
        | v2_struct_0(k2_tsep_1(X16,X15,X14))
        | ~ m1_pre_topc(k2_tsep_1(X16,X15,X14),sK0) )
    | ~ spl5_153 ),
    inference(resolution,[],[f55,f1446])).

fof(f1949,plain,
    ( spl5_18
    | spl5_219
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1896,f1574,f1947,f174])).

fof(f1947,plain,
    ( spl5_219
  <=> ! [X11,X13,X10,X12] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(k2_tsep_1(X12,X11,X10),sK0)
        | ~ m1_pre_topc(X13,sK1)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(k2_tsep_1(X12,X11,X10))
        | ~ m1_pre_topc(k2_tsep_1(X12,X11,X10),X13)
        | v2_struct_0(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12)
        | v2_struct_0(X11)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X12)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X11)
        | ~ m1_pre_topc(X11,X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_219])])).

fof(f1896,plain,
    ( ! [X12,X10,X13,X11] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X11)
        | ~ m1_pre_topc(X10,X12)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X11,X12)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(k2_tsep_1(X12,X11,X10),X13)
        | v2_struct_0(k2_tsep_1(X12,X11,X10))
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X13,sK1)
        | ~ m1_pre_topc(k2_tsep_1(X12,X11,X10),sK0) )
    | ~ spl5_167 ),
    inference(resolution,[],[f55,f1575])).

fof(f1945,plain,
    ( spl5_18
    | spl5_218
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f1895,f1822,f1943,f174])).

fof(f1943,plain,
    ( spl5_218
  <=> ! [X9,X7,X8,X6] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(k2_tsep_1(X8,X7,X6),sK0)
        | ~ m1_pre_topc(X9,sK3)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(k2_tsep_1(X8,X7,X6))
        | ~ m1_pre_topc(k2_tsep_1(X8,X7,X6),X9)
        | v2_struct_0(X9)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X7)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X8)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X7,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_218])])).

fof(f1895,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X6,X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(X8,X7,X6),X9)
        | v2_struct_0(k2_tsep_1(X8,X7,X6))
        | ~ m1_pre_topc(X9,sK0)
        | ~ m1_pre_topc(X9,sK3)
        | ~ m1_pre_topc(k2_tsep_1(X8,X7,X6),sK0) )
    | ~ spl5_200 ),
    inference(resolution,[],[f55,f1823])).

fof(f1941,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_10
    | ~ spl5_9
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_110
    | ~ spl5_5
    | ~ spl5_166 ),
    inference(avatar_split_clause,[],[f1894,f1555,f88,f909,f98,f103,f118,f123,f108,f113,f138,f143,f148])).

fof(f909,plain,
    ( spl5_110
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f1894,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_166 ),
    inference(resolution,[],[f55,f1557])).

fof(f1940,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_14
    | ~ spl5_13
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_216
    | ~ spl5_217
    | ~ spl5_165 ),
    inference(avatar_split_clause,[],[f1893,f1550,f1937,f1933,f98,f103,f118,f123,f128,f133,f138,f143,f148])).

fof(f1933,plain,
    ( spl5_216
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_216])])).

fof(f1937,plain,
    ( spl5_217
  <=> m1_pre_topc(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_217])])).

fof(f1893,plain,
    ( ~ m1_pre_topc(sK1,sK4)
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_165 ),
    inference(resolution,[],[f55,f1552])).

fof(f1931,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_19
    | ~ spl5_22
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_214
    | ~ spl5_215
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1892,f83,f1928,f1924,f98,f103,f118,f123,f200,f178,f138,f143,f148])).

fof(f178,plain,
    ( spl5_19
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f200,plain,
    ( spl5_22
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1924,plain,
    ( spl5_214
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).

fof(f1928,plain,
    ( spl5_215
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).

fof(f83,plain,
    ( spl5_4
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1892,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f55,f85])).

fof(f85,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f1922,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_213
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f1903,f644,f1920,f98,f103,f118,f123,f138,f143,f148])).

fof(f1920,plain,
    ( spl5_213
  <=> ! [X5] :
        ( ~ m1_pre_topc(X5,sK4)
        | ~ m1_pre_topc(X5,sK1)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | r1_tsep_1(X5,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f1903,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK4)
        | r1_tsep_1(X5,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X5,sK1) )
    | ~ spl5_81 ),
    inference(duplicate_literal_removal,[],[f1891])).

fof(f1891,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK4)
        | r1_tsep_1(X5,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X5,sK1)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0) )
    | ~ spl5_81 ),
    inference(resolution,[],[f55,f645])).

fof(f1918,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_212
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f1904,f1193,f1916,f98,f103,f118,f123,f138,f143,f148])).

fof(f1916,plain,
    ( spl5_212
  <=> ! [X4] :
        ( ~ m1_pre_topc(X4,sK4)
        | ~ m1_pre_topc(X4,sK3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | r1_tsep_1(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_212])])).

fof(f1904,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK4)
        | r1_tsep_1(X4,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X4,sK3) )
    | ~ spl5_134 ),
    inference(duplicate_literal_removal,[],[f1890])).

fof(f1890,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK4)
        | r1_tsep_1(X4,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X4,sK3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0) )
    | ~ spl5_134 ),
    inference(resolution,[],[f55,f1194])).

fof(f1914,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_211
    | ~ spl5_188 ),
    inference(avatar_split_clause,[],[f1905,f1734,f1912,f98,f103,f118,f123,f138,f143,f148])).

fof(f1912,plain,
    ( spl5_211
  <=> ! [X3,X2] :
        ( ~ m1_pre_topc(X2,sK4)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_211])])).

fof(f1905,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK4)
        | r1_tsep_1(X2,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl5_188 ),
    inference(duplicate_literal_removal,[],[f1889])).

fof(f1889,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK4)
        | r1_tsep_1(X2,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl5_188 ),
    inference(resolution,[],[f55,f1735])).

fof(f1910,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_210
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1906,f1770,f1908,f98,f103,f118,f123,f138,f143,f148])).

fof(f1908,plain,
    ( spl5_210
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).

fof(f1906,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl5_192 ),
    inference(duplicate_literal_removal,[],[f1888])).

fof(f1888,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_192 ),
    inference(resolution,[],[f55,f1771])).

fof(f1884,plain,
    ( spl5_18
    | spl5_209
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f1870,f1335,f1882,f174])).

fof(f1882,plain,
    ( spl5_209
  <=> ! [X9,X11,X8,X10] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | r1_tsep_1(X10,X11)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK3)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f1335,plain,
    ( spl5_146
  <=> ! [X9,X11,X10] :
        ( ~ m1_pre_topc(X9,sK3)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | ~ m1_pre_topc(X9,X11)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X10,X9)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f1870,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK3)
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X10,X11)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_146 ),
    inference(resolution,[],[f1336,f167])).

fof(f1336,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X11)
        | ~ m1_pre_topc(X9,sK3)
        | ~ m1_pre_topc(X9,X11)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X10,X9)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(X9) )
    | ~ spl5_146 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1880,plain,
    ( spl5_18
    | spl5_208
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f1869,f1335,f1878,f174])).

fof(f1878,plain,
    ( spl5_208
  <=> ! [X5,X7,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f1869,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_146 ),
    inference(resolution,[],[f1336,f50])).

fof(f1876,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_207
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f1872,f1335,f148,f143,f138,f1874,f98,f103,f118,f123])).

fof(f1874,plain,
    ( spl5_207
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f1872,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_146 ),
    inference(duplicate_literal_removal,[],[f1867])).

fof(f1867,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_146 ),
    inference(resolution,[],[f1336,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f1863,plain,
    ( spl5_18
    | spl5_206
    | ~ spl5_145 ),
    inference(avatar_split_clause,[],[f1849,f1331,f1861,f174])).

fof(f1861,plain,
    ( spl5_206
  <=> ! [X9,X11,X8,X10] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | r1_tsep_1(X11,X10)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK3)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f1331,plain,
    ( spl5_145
  <=> ! [X7,X8,X6] :
        ( ~ m1_pre_topc(X6,sK3)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f1849,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK3)
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X11,X10)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_145 ),
    inference(resolution,[],[f1332,f167])).

fof(f1332,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6) )
    | ~ spl5_145 ),
    inference(avatar_component_clause,[],[f1331])).

fof(f1859,plain,
    ( spl5_18
    | spl5_205
    | ~ spl5_145 ),
    inference(avatar_split_clause,[],[f1848,f1331,f1857,f174])).

fof(f1857,plain,
    ( spl5_205
  <=> ! [X5,X7,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | r1_tsep_1(X7,X6)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).

fof(f1848,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X7,X6)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_145 ),
    inference(resolution,[],[f1332,f50])).

fof(f1855,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_204
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_145 ),
    inference(avatar_split_clause,[],[f1851,f1331,f148,f143,f138,f1853,f98,f103,f118,f123])).

fof(f1853,plain,
    ( spl5_204
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f1851,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_145 ),
    inference(duplicate_literal_removal,[],[f1846])).

fof(f1846,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_145 ),
    inference(resolution,[],[f1332,f68])).

fof(f1845,plain,
    ( spl5_18
    | spl5_203
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f1837,f1822,f1843,f174])).

fof(f1843,plain,
    ( spl5_203
  <=> ! [X16,X18,X17,X19] :
        ( v2_struct_0(X16)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X19)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X18)
        | ~ m1_pre_topc(k2_tsep_1(X17,X18,X19),sK0)
        | ~ m1_pre_topc(X16,sK3)
        | ~ m1_pre_topc(X16,sK0)
        | v2_struct_0(k2_tsep_1(X17,X18,X19))
        | ~ m1_pre_topc(k2_tsep_1(X17,X18,X19),X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).

fof(f1837,plain,
    ( ! [X19,X17,X18,X16] :
        ( v2_struct_0(X16)
        | ~ m1_pre_topc(k2_tsep_1(X17,X18,X19),X16)
        | v2_struct_0(k2_tsep_1(X17,X18,X19))
        | ~ m1_pre_topc(X16,sK0)
        | ~ m1_pre_topc(X16,sK3)
        | ~ m1_pre_topc(k2_tsep_1(X17,X18,X19),sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X18)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | v2_struct_0(X17) )
    | ~ spl5_200 ),
    inference(resolution,[],[f1823,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1832,plain,
    ( spl5_18
    | spl5_202
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f1818,f1327,f1830,f174])).

fof(f1830,plain,
    ( spl5_202
  <=> ! [X9,X11,X8,X10] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | ~ m1_pre_topc(X10,X11)
        | r1_tsep_1(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,sK3)
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).

fof(f1327,plain,
    ( spl5_144
  <=> ! [X3,X5,X4] :
        ( ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f1818,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK3)
        | r1_tsep_1(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X10,X11)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_144 ),
    inference(resolution,[],[f1328,f167])).

fof(f1328,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X3,sK3)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) )
    | ~ spl5_144 ),
    inference(avatar_component_clause,[],[f1327])).

fof(f1828,plain,
    ( spl5_18
    | spl5_201
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f1817,f1327,f1826,f174])).

fof(f1826,plain,
    ( spl5_201
  <=> ! [X5,X7,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | ~ m1_pre_topc(X6,X7)
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f1817,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK3)
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_144 ),
    inference(resolution,[],[f1328,f50])).

fof(f1824,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_200
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f1820,f1327,f148,f143,f138,f1822,f98,f103,f118,f123])).

fof(f1820,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_144 ),
    inference(duplicate_literal_removal,[],[f1815])).

fof(f1815,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_144 ),
    inference(resolution,[],[f1328,f68])).

fof(f1810,plain,
    ( spl5_18
    | spl5_199
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1786,f1770,f1808,f174])).

fof(f1808,plain,
    ( spl5_199
  <=> ! [X16,X15,X17,X14] :
        ( v2_struct_0(X14)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X17)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | ~ m1_pre_topc(X15,X17)
        | ~ m1_pre_topc(X16,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X16,X15)
        | ~ m1_pre_topc(X15,sK0)
        | ~ m1_pre_topc(X14,sK3)
        | ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).

fof(f1786,plain,
    ( ! [X14,X17,X15,X16] :
        ( v2_struct_0(X14)
        | ~ m1_pre_topc(X15,X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X14,sK0)
        | ~ m1_pre_topc(X14,sK3)
        | ~ m1_pre_topc(X15,sK0)
        | r1_tsep_1(X16,X15)
        | ~ m1_pre_topc(X16,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X15,X17)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X16,X17)
        | v2_struct_0(X16)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | v2_struct_0(X17) )
    | ~ spl5_192 ),
    inference(duplicate_literal_removal,[],[f1785])).

fof(f1785,plain,
    ( ! [X14,X17,X15,X16] :
        ( v2_struct_0(X14)
        | ~ m1_pre_topc(X15,X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X14,sK0)
        | ~ m1_pre_topc(X14,sK3)
        | ~ m1_pre_topc(X15,sK0)
        | r1_tsep_1(X16,X15)
        | ~ m1_pre_topc(X16,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X15,X17)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X16,X17)
        | v2_struct_0(X16)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | v2_struct_0(X17) )
    | ~ spl5_192 ),
    inference(resolution,[],[f1771,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f1806,plain,
    ( spl5_18
    | spl5_198
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1787,f1770,f1804,f174])).

fof(f1804,plain,
    ( spl5_198
  <=> ! [X11,X13,X10,X12] :
        ( v2_struct_0(X10)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X13)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X13)
        | ~ m1_pre_topc(X11,X13)
        | ~ m1_pre_topc(X12,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X11,X12)
        | ~ m1_pre_topc(X11,sK0)
        | ~ m1_pre_topc(X10,sK3)
        | ~ m1_pre_topc(X10,sK0)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f1787,plain,
    ( ! [X12,X10,X13,X11] :
        ( v2_struct_0(X10)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X10,sK0)
        | ~ m1_pre_topc(X10,sK3)
        | ~ m1_pre_topc(X11,sK0)
        | r1_tsep_1(X11,X12)
        | ~ m1_pre_topc(X12,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,X13)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X13)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X12,X13)
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | v2_struct_0(X13) )
    | ~ spl5_192 ),
    inference(duplicate_literal_removal,[],[f1784])).

fof(f1784,plain,
    ( ! [X12,X10,X13,X11] :
        ( v2_struct_0(X10)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X10,sK0)
        | ~ m1_pre_topc(X10,sK3)
        | ~ m1_pre_topc(X11,sK0)
        | r1_tsep_1(X11,X12)
        | ~ m1_pre_topc(X12,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,X13)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X13)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X12,X13)
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | v2_struct_0(X13) )
    | ~ spl5_192 ),
    inference(resolution,[],[f1771,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1802,plain,
    ( spl5_18
    | spl5_197
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1788,f1770,f1800,f174])).

fof(f1800,plain,
    ( spl5_197
  <=> ! [X9,X7,X8,X6] :
        ( v2_struct_0(X6)
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X9)
        | ~ m1_pre_topc(X7,X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9)
        | r1_tsep_1(X8,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(X7,sK0)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).

fof(f1788,plain,
    ( ! [X6,X8,X7,X9] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X6,sK0)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(X7,sK0)
        | r1_tsep_1(X8,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X9)
        | ~ m1_pre_topc(X8,X9)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | v2_struct_0(X9) )
    | ~ spl5_192 ),
    inference(duplicate_literal_removal,[],[f1783])).

fof(f1783,plain,
    ( ! [X6,X8,X7,X9] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X6,sK0)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(X7,sK0)
        | r1_tsep_1(X8,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X9)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X8,X9)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | v2_struct_0(X9) )
    | ~ spl5_192 ),
    inference(resolution,[],[f1771,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1798,plain,
    ( spl5_18
    | spl5_196
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1789,f1770,f1796,f174])).

fof(f1796,plain,
    ( spl5_196
  <=> ! [X3,X5,X2,X4] :
        ( v2_struct_0(X2)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).

fof(f1789,plain,
    ( ! [X4,X2,X5,X3] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_192 ),
    inference(duplicate_literal_removal,[],[f1782])).

fof(f1782,plain,
    ( ! [X4,X2,X5,X3] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_192 ),
    inference(resolution,[],[f1771,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1794,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_195
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1790,f1770,f1792,f118,f123,f98,f103,f138,f143,f148])).

fof(f1792,plain,
    ( spl5_195
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_195])])).

fof(f1790,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_192 ),
    inference(duplicate_literal_removal,[],[f1781])).

fof(f1781,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_192 ),
    inference(resolution,[],[f1771,f54])).

fof(f1780,plain,
    ( spl5_18
    | spl5_194
    | ~ spl5_143 ),
    inference(avatar_split_clause,[],[f1766,f1323,f1778,f174])).

fof(f1778,plain,
    ( spl5_194
  <=> ! [X9,X11,X8,X10] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | ~ m1_pre_topc(X10,X11)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(X11,sK3)
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f1323,plain,
    ( spl5_143
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f1766,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(X10,X11)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_143 ),
    inference(resolution,[],[f1324,f167])).

fof(f1324,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl5_143 ),
    inference(avatar_component_clause,[],[f1323])).

fof(f1776,plain,
    ( spl5_18
    | spl5_193
    | ~ spl5_143 ),
    inference(avatar_split_clause,[],[f1765,f1323,f1774,f174])).

fof(f1774,plain,
    ( spl5_193
  <=> ! [X5,X7,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | ~ m1_pre_topc(X6,X7)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).

fof(f1765,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(X6,X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_143 ),
    inference(resolution,[],[f1324,f50])).

fof(f1772,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_192
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_143 ),
    inference(avatar_split_clause,[],[f1768,f1323,f148,f143,f138,f1770,f98,f103,f118,f123])).

fof(f1768,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_143 ),
    inference(duplicate_literal_removal,[],[f1763])).

fof(f1763,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_143 ),
    inference(resolution,[],[f1324,f68])).

fof(f1758,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_191
    | ~ spl5_188 ),
    inference(avatar_split_clause,[],[f1754,f1734,f1756,f118,f123,f98,f103,f138,f143,f148])).

fof(f1756,plain,
    ( spl5_191
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).

fof(f1754,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_188 ),
    inference(duplicate_literal_removal,[],[f1745])).

fof(f1745,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_188 ),
    inference(resolution,[],[f1735,f54])).

fof(f1744,plain,
    ( spl5_18
    | spl5_190
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f1730,f959,f1742,f174])).

fof(f1742,plain,
    ( spl5_190
  <=> ! [X9,X11,X8,X10] :
        ( ~ m1_pre_topc(X8,sK0)
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | ~ m1_pre_topc(X11,X8)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X11)
        | ~ m1_pre_topc(X8,k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | v2_struct_0(X11)
        | v2_struct_0(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X8,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f959,plain,
    ( spl5_115
  <=> ! [X1,X0,X2] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f1730,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ m1_pre_topc(X8,sK0)
        | ~ m1_pre_topc(X8,sK1)
        | v2_struct_0(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X11)
        | ~ m1_pre_topc(X11,X8)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | v2_struct_0(X9) )
    | ~ spl5_115 ),
    inference(resolution,[],[f960,f167])).

fof(f960,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl5_115 ),
    inference(avatar_component_clause,[],[f959])).

fof(f1740,plain,
    ( spl5_18
    | spl5_189
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f1729,f959,f1738,f174])).

fof(f1738,plain,
    ( spl5_189
  <=> ! [X5,X7,X4,X6] :
        ( ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,X4)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X4,k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | v2_struct_0(X4)
        | v2_struct_0(X7)
        | v2_struct_0(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | ~ l1_pre_topc(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | ~ v2_pre_topc(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | ~ m1_pre_topc(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_189])])).

fof(f1729,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X4,sK1)
        | v2_struct_0(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | ~ v2_pre_topc(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | ~ l1_pre_topc(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X7,X4)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_115 ),
    inference(resolution,[],[f960,f50])).

fof(f1736,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | spl5_188
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f1732,f959,f1734,f148,f143,f138,f98,f103,f118,f123])).

fof(f1732,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_115 ),
    inference(duplicate_literal_removal,[],[f1727])).

fof(f1727,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_115 ),
    inference(resolution,[],[f960,f68])).

fof(f1723,plain,
    ( spl5_18
    | spl5_187
    | ~ spl5_89 ),
    inference(avatar_split_clause,[],[f1709,f702,f1721,f174])).

fof(f1721,plain,
    ( spl5_187
  <=> ! [X9,X11,X8,X10] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | r1_tsep_1(X10,X11)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK1)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f702,plain,
    ( spl5_89
  <=> ! [X7,X8,X6] :
        ( ~ m1_pre_topc(X6,sK1)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X7,X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f1709,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK1)
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X10,X11)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_89 ),
    inference(resolution,[],[f703,f167])).

fof(f703,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_pre_topc(X6,sK1)
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X7,X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6) )
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f702])).

fof(f1719,plain,
    ( spl5_18
    | spl5_186
    | ~ spl5_89 ),
    inference(avatar_split_clause,[],[f1708,f702,f1717,f174])).

fof(f1717,plain,
    ( spl5_186
  <=> ! [X5,X7,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).

fof(f1708,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_89 ),
    inference(resolution,[],[f703,f50])).

fof(f1715,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_185
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_89 ),
    inference(avatar_split_clause,[],[f1711,f702,f148,f143,f138,f1713,f98,f103,f118,f123])).

fof(f1713,plain,
    ( spl5_185
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).

fof(f1711,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_89 ),
    inference(duplicate_literal_removal,[],[f1706])).

fof(f1706,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_89 ),
    inference(resolution,[],[f703,f68])).

fof(f1702,plain,
    ( spl5_18
    | spl5_184
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f1688,f698,f1700,f174])).

fof(f1700,plain,
    ( spl5_184
  <=> ! [X9,X11,X8,X10] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | r1_tsep_1(X11,X10)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK1)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f698,plain,
    ( spl5_88
  <=> ! [X3,X5,X4] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X3,X4)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f1688,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK1)
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X11,X10)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_88 ),
    inference(resolution,[],[f699,f167])).

fof(f699,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X3,X4)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) )
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f698])).

fof(f1698,plain,
    ( spl5_18
    | spl5_183
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f1687,f698,f1696,f174])).

fof(f1696,plain,
    ( spl5_183
  <=> ! [X5,X7,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | r1_tsep_1(X7,X6)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).

fof(f1687,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X7,X6)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_88 ),
    inference(resolution,[],[f699,f50])).

fof(f1694,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_182
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f1690,f698,f148,f143,f138,f1692,f98,f103,f118,f123])).

fof(f1692,plain,
    ( spl5_182
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,sK1)
        | r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).

fof(f1690,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_88 ),
    inference(duplicate_literal_removal,[],[f1685])).

fof(f1685,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_88 ),
    inference(resolution,[],[f699,f68])).

fof(f1657,plain,
    ( spl5_18
    | spl5_181
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f1616,f867,f1655,f174])).

fof(f1655,plain,
    ( spl5_181
  <=> ! [X9,X11,X10] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9)
        | ~ m1_pre_topc(k2_tsep_1(X11,X9,X10),sK0)
        | v2_struct_0(k2_tsep_1(X11,X9,X10))
        | ~ m1_pre_topc(k2_tsep_1(X11,X9,X10),sK1)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(X10)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X11)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(X10,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).

fof(f1616,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(X9,X11)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X10,X11)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(k2_tsep_1(X11,X9,X10),sK1)
        | v2_struct_0(k2_tsep_1(X11,X9,X10))
        | ~ m1_pre_topc(k2_tsep_1(X11,X9,X10),sK0) )
    | ~ spl5_106 ),
    inference(resolution,[],[f54,f868])).

fof(f1653,plain,
    ( spl5_18
    | spl5_180
    | ~ spl5_153 ),
    inference(avatar_split_clause,[],[f1615,f1445,f1651,f174])).

fof(f1651,plain,
    ( spl5_180
  <=> ! [X7,X8,X6] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(k2_tsep_1(X8,X6,X7),sK0)
        | v2_struct_0(k2_tsep_1(X8,X6,X7))
        | ~ m1_pre_topc(k2_tsep_1(X8,X6,X7),sK3)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X7)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X8)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X7,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f1615,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X6,X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(k2_tsep_1(X8,X6,X7),sK3)
        | v2_struct_0(k2_tsep_1(X8,X6,X7))
        | ~ m1_pre_topc(k2_tsep_1(X8,X6,X7),sK0) )
    | ~ spl5_153 ),
    inference(resolution,[],[f54,f1446])).

fof(f1649,plain,
    ( spl5_18
    | spl5_179
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1614,f1574,f1647,f174])).

fof(f1647,plain,
    ( spl5_179
  <=> ! [X3,X5,X2,X4] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(k2_tsep_1(X4,X2,X3),sK0)
        | ~ m1_pre_topc(X5,sK1)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(k2_tsep_1(X4,X2,X3))
        | ~ m1_pre_topc(k2_tsep_1(X4,X2,X3),X5)
        | v2_struct_0(X5)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X4)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_179])])).

fof(f1614,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X2,X4)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X3,X4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(X4,X2,X3),X5)
        | v2_struct_0(k2_tsep_1(X4,X2,X3))
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X5,sK1)
        | ~ m1_pre_topc(k2_tsep_1(X4,X2,X3),sK0) )
    | ~ spl5_167 ),
    inference(resolution,[],[f54,f1575])).

fof(f1645,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_10
    | ~ spl5_9
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_177
    | ~ spl5_178
    | ~ spl5_166 ),
    inference(avatar_split_clause,[],[f1613,f1555,f1642,f1638,f118,f123,f98,f103,f108,f113,f138,f143,f148])).

fof(f1638,plain,
    ( spl5_177
  <=> r1_tsep_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f1642,plain,
    ( spl5_178
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f1613,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | r1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_166 ),
    inference(resolution,[],[f54,f1557])).

fof(f1636,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_14
    | ~ spl5_13
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_58
    | ~ spl5_6
    | ~ spl5_165 ),
    inference(avatar_split_clause,[],[f1612,f1550,f93,f437,f118,f123,f98,f103,f128,f133,f138,f143,f148])).

fof(f437,plain,
    ( spl5_58
  <=> r1_tsep_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f1612,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | r1_tsep_1(sK1,sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_165 ),
    inference(resolution,[],[f54,f1552])).

fof(f1635,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_19
    | ~ spl5_22
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_175
    | ~ spl5_176
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1611,f83,f1632,f1628,f118,f123,f98,f103,f200,f178,f138,f143,f148])).

fof(f1628,plain,
    ( spl5_175
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f1632,plain,
    ( spl5_176
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f1611,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f54,f85])).

fof(f1626,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_8
    | ~ spl5_7
    | spl5_12
    | ~ spl5_11
    | spl5_174
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f1622,f1193,f1624,f118,f123,f98,f103,f138,f143,f148])).

fof(f1624,plain,
    ( spl5_174
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f1622,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl5_134 ),
    inference(duplicate_literal_removal,[],[f1609])).

fof(f1609,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_134 ),
    inference(resolution,[],[f54,f1194])).

fof(f1608,plain,
    ( spl5_18
    | spl5_173
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1589,f1574,f1606,f174])).

fof(f1606,plain,
    ( spl5_173
  <=> ! [X13,X15,X12,X14] :
        ( v2_struct_0(X12)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X15)
        | ~ m1_pre_topc(X13,X15)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X15)
        | r1_tsep_1(X14,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X14,X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK1)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f1589,plain,
    ( ! [X14,X12,X15,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X12,sK0)
        | ~ m1_pre_topc(X12,sK1)
        | ~ m1_pre_topc(X13,sK0)
        | r1_tsep_1(X14,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X14,X13)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X15)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X13,X15)
        | ~ m1_pre_topc(X14,X15)
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | v2_struct_0(X15) )
    | ~ spl5_167 ),
    inference(duplicate_literal_removal,[],[f1588])).

fof(f1588,plain,
    ( ! [X14,X12,X15,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X12,sK0)
        | ~ m1_pre_topc(X12,sK1)
        | ~ m1_pre_topc(X13,sK0)
        | r1_tsep_1(X14,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X14,X13)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X15)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X13,X15)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X14,X15)
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | v2_struct_0(X15) )
    | ~ spl5_167 ),
    inference(resolution,[],[f1575,f58])).

fof(f1604,plain,
    ( spl5_18
    | spl5_172
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1590,f1574,f1602,f174])).

fof(f1602,plain,
    ( spl5_172
  <=> ! [X9,X11,X8,X10] :
        ( v2_struct_0(X8)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X11)
        | ~ m1_pre_topc(X9,X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(X10,X9)
        | ~ m1_pre_topc(X9,sK0)
        | ~ m1_pre_topc(X8,sK1)
        | ~ m1_pre_topc(X8,sK0)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f1590,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(X8)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X8,sK0)
        | ~ m1_pre_topc(X8,sK1)
        | ~ m1_pre_topc(X9,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(X10,X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X9,X11)
        | ~ m1_pre_topc(X10,X11)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11)
        | v2_struct_0(X11) )
    | ~ spl5_167 ),
    inference(duplicate_literal_removal,[],[f1587])).

fof(f1587,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(X8)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X8,sK0)
        | ~ m1_pre_topc(X8,sK1)
        | ~ m1_pre_topc(X9,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(X10,X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X9,X11)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X10,X11)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11)
        | v2_struct_0(X11) )
    | ~ spl5_167 ),
    inference(resolution,[],[f1575,f59])).

fof(f1600,plain,
    ( spl5_18
    | spl5_171
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1591,f1574,f1598,f174])).

fof(f1598,plain,
    ( spl5_171
  <=> ! [X5,X7,X4,X6] :
        ( v2_struct_0(X4)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X5,X7)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X6,X5)
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f1591,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(X4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X5,sK0)
        | r1_tsep_1(X6,X5)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X5,X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X7)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl5_167 ),
    inference(duplicate_literal_removal,[],[f1586])).

fof(f1586,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(X4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X5,sK0)
        | r1_tsep_1(X6,X5)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X5,X7)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X7)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl5_167 ),
    inference(resolution,[],[f1575,f60])).

fof(f1596,plain,
    ( spl5_18
    | spl5_170
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1592,f1574,f1594,f174])).

fof(f1594,plain,
    ( spl5_170
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X1,X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).

fof(f1592,plain,
    ( ! [X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,X2)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_167 ),
    inference(duplicate_literal_removal,[],[f1585])).

fof(f1585,plain,
    ( ! [X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,X2)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_167 ),
    inference(resolution,[],[f1575,f61])).

fof(f1584,plain,
    ( spl5_18
    | spl5_169
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f1570,f694,f1582,f174])).

fof(f1582,plain,
    ( spl5_169
  <=> ! [X9,X11,X8,X10] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | ~ m1_pre_topc(X10,X11)
        | r1_tsep_1(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X11,sK1)
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f694,plain,
    ( spl5_87
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f1570,plain,
    ( ! [X10,X8,X11,X9] :
        ( v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X11,sK1)
        | r1_tsep_1(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X10,X11)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_87 ),
    inference(resolution,[],[f695,f167])).

fof(f695,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f694])).

fof(f1580,plain,
    ( spl5_18
    | spl5_168
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f1569,f694,f1578,f174])).

fof(f1578,plain,
    ( spl5_168
  <=> ! [X5,X7,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | ~ m1_pre_topc(X6,X7)
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_168])])).

fof(f1569,plain,
    ( ! [X6,X4,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5))
        | ~ m1_pre_topc(X7,sK1)
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_87 ),
    inference(resolution,[],[f695,f50])).

fof(f1576,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | spl5_167
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f1572,f694,f148,f143,f138,f1574,f98,f103,f118,f123])).

fof(f1572,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_87 ),
    inference(duplicate_literal_removal,[],[f1567])).

fof(f1567,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK1)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_87 ),
    inference(resolution,[],[f695,f68])).

fof(f1558,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_14
    | ~ spl5_13
    | ~ spl5_9
    | spl5_166
    | spl5_10
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1547,f1531,f113,f1555,f108,f128,f133,f138,f143,f148])).

fof(f1531,plain,
    ( spl5_162
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f1547,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_162 ),
    inference(duplicate_literal_removal,[],[f1543])).

fof(f1543,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_162 ),
    inference(resolution,[],[f1532,f167])).

fof(f1532,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_162 ),
    inference(avatar_component_clause,[],[f1531])).

fof(f1553,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_10
    | ~ spl5_9
    | ~ spl5_13
    | spl5_165
    | spl5_14
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1548,f1531,f133,f1550,f128,f108,f113,f138,f143,f148])).

fof(f1548,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_162 ),
    inference(duplicate_literal_removal,[],[f1542])).

fof(f1542,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_162 ),
    inference(resolution,[],[f1532,f50])).

fof(f1541,plain,
    ( spl5_18
    | spl5_164
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f1527,f963,f1539,f174])).

fof(f1539,plain,
    ( spl5_164
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f963,plain,
    ( spl5_116
  <=> ! [X3,X4] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X4)
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f1527,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_116 ),
    inference(resolution,[],[f964,f167])).

fof(f964,plain,
    ( ! [X4,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X4)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X4)
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl5_116 ),
    inference(avatar_component_clause,[],[f963])).

fof(f1537,plain,
    ( spl5_18
    | spl5_163
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f1526,f963,f1535,f174])).

fof(f1535,plain,
    ( spl5_163
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f1526,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_116 ),
    inference(resolution,[],[f964,f50])).

fof(f1533,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_22
    | spl5_162
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f1529,f963,f148,f143,f138,f1531,f200,f98,f103,f118,f123])).

fof(f1529,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_116 ),
    inference(duplicate_literal_removal,[],[f1524])).

fof(f1524,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_116 ),
    inference(resolution,[],[f964,f68])).

fof(f1502,plain,
    ( spl5_18
    | spl5_161
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f1488,f972,f1500,f174])).

fof(f1500,plain,
    ( spl5_161
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(sK3,X7)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f972,plain,
    ( spl5_118
  <=> ! [X9,X10] :
        ( r1_tsep_1(sK3,X9)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X10)
        | ~ m1_pre_topc(sK3,X10)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | ~ m1_pre_topc(X9,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f1488,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(sK3,X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_118 ),
    inference(resolution,[],[f973,f167])).

fof(f973,plain,
    ( ! [X10,X9] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X10)
        | ~ m1_pre_topc(sK3,X10)
        | r1_tsep_1(sK3,X9)
        | ~ m1_pre_topc(X9,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f972])).

fof(f1498,plain,
    ( spl5_18
    | spl5_160
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f1487,f972,f1496,f174])).

fof(f1496,plain,
    ( spl5_160
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(sK3,X4)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f1487,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(sK3,X4)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_118 ),
    inference(resolution,[],[f973,f50])).

fof(f1494,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_9
    | spl5_159
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f1490,f972,f148,f143,f138,f1492,f108,f98,f103,f118,f123])).

fof(f1492,plain,
    ( spl5_159
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f1490,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_118 ),
    inference(duplicate_literal_removal,[],[f1485])).

fof(f1485,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_118 ),
    inference(resolution,[],[f973,f68])).

fof(f1481,plain,
    ( spl5_18
    | spl5_158
    | ~ spl5_117 ),
    inference(avatar_split_clause,[],[f1467,f968,f1479,f174])).

fof(f1479,plain,
    ( spl5_158
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(sK1,X7)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f968,plain,
    ( spl5_117
  <=> ! [X7,X8] :
        ( r1_tsep_1(sK1,X7)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_pre_topc(sK1,X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f1467,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(sK1,X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_117 ),
    inference(resolution,[],[f969,f167])).

fof(f969,plain,
    ( ! [X8,X7] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_pre_topc(sK1,X8)
        | r1_tsep_1(sK1,X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_117 ),
    inference(avatar_component_clause,[],[f968])).

fof(f1477,plain,
    ( spl5_18
    | spl5_157
    | ~ spl5_117 ),
    inference(avatar_split_clause,[],[f1466,f968,f1475,f174])).

fof(f1475,plain,
    ( spl5_157
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(sK1,X4)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f1466,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(sK1,X4)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_117 ),
    inference(resolution,[],[f969,f50])).

fof(f1473,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_13
    | spl5_156
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_117 ),
    inference(avatar_split_clause,[],[f1469,f968,f148,f143,f138,f1471,f128,f98,f103,f118,f123])).

fof(f1471,plain,
    ( spl5_156
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f1469,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_117 ),
    inference(duplicate_literal_removal,[],[f1464])).

fof(f1464,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_117 ),
    inference(resolution,[],[f969,f68])).

fof(f1455,plain,
    ( spl5_18
    | spl5_155
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f1441,f492,f1453,f174])).

fof(f1453,plain,
    ( spl5_155
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f492,plain,
    ( spl5_67
  <=> ! [X5,X4] :
        ( r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ m1_pre_topc(X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f1441,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_67 ),
    inference(resolution,[],[f493,f167])).

fof(f493,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X5)
        | ~ m1_pre_topc(X4,sK3) )
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f492])).

fof(f1451,plain,
    ( spl5_18
    | spl5_154
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f1440,f492,f1449,f174])).

fof(f1449,plain,
    ( spl5_154
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f1440,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_67 ),
    inference(resolution,[],[f493,f50])).

fof(f1447,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_9
    | spl5_153
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f1443,f492,f148,f143,f138,f1445,f108,f98,f103,f118,f123])).

fof(f1443,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_67 ),
    inference(duplicate_literal_removal,[],[f1438])).

fof(f1438,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_67 ),
    inference(resolution,[],[f493,f68])).

fof(f1422,plain,
    ( spl5_10
    | spl5_152
    | ~ spl5_119 ),
    inference(avatar_split_clause,[],[f1409,f976,f1420,f113])).

fof(f1420,plain,
    ( spl5_152
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X8,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(sK3,X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).

fof(f976,plain,
    ( spl5_119
  <=> ! [X11,X12] :
        ( r1_tsep_1(sK3,X11)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X12)
        | ~ m1_pre_topc(sK3,X12)
        | ~ m1_pre_topc(sK1,X12)
        | ~ m1_pre_topc(X11,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f1409,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(sK3,X8)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(X8,sK1)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_119 ),
    inference(resolution,[],[f977,f167])).

fof(f977,plain,
    ( ! [X12,X11] :
        ( ~ m1_pre_topc(sK3,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X12)
        | r1_tsep_1(sK3,X11)
        | ~ m1_pre_topc(sK1,X12)
        | ~ m1_pre_topc(X11,sK1) )
    | ~ spl5_119 ),
    inference(avatar_component_clause,[],[f976])).

fof(f1418,plain,
    ( spl5_10
    | spl5_151
    | ~ spl5_119 ),
    inference(avatar_split_clause,[],[f1408,f976,f1416,f113])).

fof(f1416,plain,
    ( spl5_151
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X5,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(sK3,X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f1408,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(sK3,X5)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(X5,sK1)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_119 ),
    inference(resolution,[],[f977,f50])).

fof(f1414,plain,
    ( ~ spl5_13
    | spl5_150
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_9
    | ~ spl5_119 ),
    inference(avatar_split_clause,[],[f1406,f976,f108,f148,f143,f138,f1412,f128])).

fof(f1412,plain,
    ( spl5_150
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | r1_tsep_1(sK3,X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f1406,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(sK3,X1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl5_9
    | ~ spl5_119 ),
    inference(resolution,[],[f977,f110])).

fof(f1401,plain,
    ( spl5_10
    | spl5_149
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f1388,f676,f1399,f113])).

fof(f1399,plain,
    ( spl5_149
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X8,sK3)
        | r1_tsep_1(X8,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f676,plain,
    ( spl5_86
  <=> ! [X5,X4] :
        ( r1_tsep_1(X4,sK1)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(sK1,X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ m1_pre_topc(X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f1388,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(X8,sK1)
        | ~ m1_pre_topc(X8,sK3)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_86 ),
    inference(resolution,[],[f677,f167])).

fof(f677,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(sK1,X5)
        | r1_tsep_1(X4,sK1)
        | ~ m1_pre_topc(X4,sK3) )
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f676])).

fof(f1397,plain,
    ( spl5_10
    | spl5_148
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f1387,f676,f1395,f113])).

fof(f1395,plain,
    ( spl5_148
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X5,sK3)
        | r1_tsep_1(X5,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f1387,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(X5,sK1)
        | ~ m1_pre_topc(X5,sK3)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_86 ),
    inference(resolution,[],[f677,f50])).

fof(f1393,plain,
    ( ~ spl5_13
    | spl5_147
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_9
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f1385,f676,f108,f148,f143,f138,f1391,f128])).

fof(f1391,plain,
    ( spl5_147
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).

fof(f1385,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(X1,sK1)
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl5_9
    | ~ spl5_86 ),
    inference(resolution,[],[f677,f110])).

fof(f1348,plain,
    ( ~ spl5_9
    | spl5_1
    | spl5_10
    | ~ spl5_5
    | ~ spl5_140 ),
    inference(avatar_split_clause,[],[f1347,f1295,f88,f113,f70,f108])).

fof(f1295,plain,
    ( spl5_140
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f1347,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl5_5
    | ~ spl5_140 ),
    inference(resolution,[],[f1296,f90])).

fof(f90,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1296,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_140 ),
    inference(avatar_component_clause,[],[f1295])).

fof(f1337,plain,
    ( spl5_18
    | spl5_146
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f1318,f1193,f1335,f174])).

fof(f1318,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_pre_topc(X9,sK3)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | r1_tsep_1(X10,X9)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X9,X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X10,X11)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11)
        | v2_struct_0(X11) )
    | ~ spl5_134 ),
    inference(duplicate_literal_removal,[],[f1317])).

fof(f1317,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_pre_topc(X9,sK3)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | r1_tsep_1(X10,X9)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X9,X11)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X10,X11)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11)
        | v2_struct_0(X11) )
    | ~ spl5_134 ),
    inference(resolution,[],[f1194,f58])).

fof(f1333,plain,
    ( spl5_18
    | spl5_145
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f1319,f1193,f1331,f174])).

fof(f1319,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(X6,sK3)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_134 ),
    inference(duplicate_literal_removal,[],[f1316])).

fof(f1316,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(X6,sK3)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_134 ),
    inference(resolution,[],[f1194,f59])).

fof(f1329,plain,
    ( spl5_18
    | spl5_144
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f1320,f1193,f1327,f174])).

fof(f1320,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_134 ),
    inference(duplicate_literal_removal,[],[f1315])).

fof(f1315,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_134 ),
    inference(resolution,[],[f1194,f60])).

fof(f1325,plain,
    ( spl5_18
    | spl5_143
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f1321,f1193,f1323,f174])).

fof(f1321,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_134 ),
    inference(duplicate_literal_removal,[],[f1314])).

fof(f1314,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_134 ),
    inference(resolution,[],[f1194,f61])).

fof(f1305,plain,
    ( spl5_8
    | spl5_142
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f1292,f1039,f1303,f103])).

fof(f1303,plain,
    ( spl5_142
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK4)
        | r1_tsep_1(sK2,X7)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1039,plain,
    ( spl5_123
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK2,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f1292,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(sK2,X7)
        | ~ m1_pre_topc(X7,sK4)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_123 ),
    inference(resolution,[],[f1040,f167])).

fof(f1040,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl5_123 ),
    inference(avatar_component_clause,[],[f1039])).

fof(f1301,plain,
    ( spl5_8
    | spl5_141
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f1291,f1039,f1299,f103])).

fof(f1299,plain,
    ( spl5_141
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK4)
        | r1_tsep_1(sK2,X4)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f1291,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(sK2,X4)
        | ~ m1_pre_topc(X4,sK4)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_123 ),
    inference(resolution,[],[f1040,f50])).

fof(f1297,plain,
    ( ~ spl5_11
    | spl5_140
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_7
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f1289,f1039,f98,f148,f143,f138,f1295,f118])).

fof(f1289,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl5_7
    | ~ spl5_123 ),
    inference(resolution,[],[f1040,f100])).

fof(f100,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f1268,plain,
    ( spl5_10
    | ~ spl5_102
    | spl5_139
    | ~ spl5_131 ),
    inference(avatar_split_clause,[],[f1260,f1153,f1266,f832,f113])).

fof(f832,plain,
    ( spl5_102
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f1266,plain,
    ( spl5_139
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK3,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK3,X2,X3),sK0)
        | r1_tsep_1(sK1,k2_tsep_1(sK3,X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f1153,plain,
    ( spl5_131
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(sK1,X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f1260,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK3,X2,X3))
        | r1_tsep_1(sK1,k2_tsep_1(sK3,X2,X3))
        | ~ m1_pre_topc(k2_tsep_1(sK3,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl5_131 ),
    inference(resolution,[],[f1154,f68])).

fof(f1154,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X1)
        | r1_tsep_1(sK1,X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f1153])).

fof(f1264,plain,
    ( spl5_10
    | ~ spl5_102
    | spl5_138
    | ~ spl5_131 ),
    inference(avatar_split_clause,[],[f1259,f1153,f1262,f832,f113])).

fof(f1262,plain,
    ( spl5_138
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK3,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(k1_tsep_1(sK3,X0,X1),sK0)
        | r1_tsep_1(sK1,k1_tsep_1(sK3,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f1259,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK3,X0,X1))
        | r1_tsep_1(sK1,k1_tsep_1(sK3,X0,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK3,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl5_131 ),
    inference(resolution,[],[f1154,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f1233,plain,
    ( ~ spl5_9
    | spl5_10
    | ~ spl5_137
    | spl5_50
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f1228,f867,f396,f1230,f113,f108])).

fof(f1230,plain,
    ( spl5_137
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f396,plain,
    ( spl5_50
  <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f1228,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | spl5_50
    | ~ spl5_106 ),
    inference(resolution,[],[f397,f868])).

fof(f397,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | spl5_50 ),
    inference(avatar_component_clause,[],[f396])).

fof(f1203,plain,
    ( spl5_18
    | spl5_136
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1189,f488,f1201,f174])).

fof(f1201,plain,
    ( spl5_136
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f488,plain,
    ( spl5_66
  <=> ! [X3,X2] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f1189,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_66 ),
    inference(resolution,[],[f489,f167])).

fof(f489,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(X2,sK3) )
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f488])).

fof(f1199,plain,
    ( spl5_18
    | spl5_135
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1188,f488,f1197,f174])).

fof(f1197,plain,
    ( spl5_135
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).

fof(f1188,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_66 ),
    inference(resolution,[],[f489,f50])).

fof(f1195,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_9
    | spl5_134
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1191,f488,f148,f143,f138,f1193,f108,f98,f103,f118,f123])).

fof(f1191,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_66 ),
    inference(duplicate_literal_removal,[],[f1186])).

fof(f1186,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_66 ),
    inference(resolution,[],[f489,f68])).

fof(f1167,plain,
    ( spl5_14
    | spl5_10
    | spl5_119
    | ~ spl5_111 ),
    inference(avatar_split_clause,[],[f1068,f924,f976,f113,f133])).

fof(f924,plain,
    ( spl5_111
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f1068,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(sK3,X4)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X5)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_111 ),
    inference(resolution,[],[f926,f59])).

fof(f926,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f924])).

fof(f1166,plain,
    ( spl5_10
    | spl5_14
    | spl5_86
    | ~ spl5_111 ),
    inference(avatar_split_clause,[],[f1067,f924,f676,f133,f113])).

fof(f1067,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,sK1)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_111 ),
    inference(resolution,[],[f926,f60])).

fof(f1165,plain,
    ( spl5_10
    | spl5_14
    | spl5_85
    | ~ spl5_111 ),
    inference(avatar_split_clause,[],[f1066,f924,f672,f133,f113])).

fof(f672,plain,
    ( spl5_85
  <=> ! [X3,X2] :
        ( r1_tsep_1(sK1,X2)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f1066,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_111 ),
    inference(resolution,[],[f926,f61])).

fof(f1164,plain,
    ( spl5_14
    | spl5_10
    | spl5_84
    | ~ spl5_111 ),
    inference(avatar_split_clause,[],[f1069,f924,f668,f113,f133])).

fof(f668,plain,
    ( spl5_84
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK3)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f1069,plain,
    ( ! [X6,X7] :
        ( r1_tsep_1(X6,sK3)
        | ~ m1_pre_topc(X6,sK1)
        | ~ m1_pre_topc(sK3,X7)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X7)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X6,X7)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl5_111 ),
    inference(resolution,[],[f926,f58])).

fof(f1163,plain,
    ( spl5_10
    | spl5_133
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f1150,f672,f1161,f113])).

fof(f1161,plain,
    ( spl5_133
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X8,sK3)
        | r1_tsep_1(sK1,X8)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f1150,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(sK1,X8)
        | ~ m1_pre_topc(X8,sK3)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_85 ),
    inference(resolution,[],[f673,f167])).

fof(f673,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK1,X3)
        | r1_tsep_1(sK1,X2)
        | ~ m1_pre_topc(X2,sK3) )
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f672])).

fof(f1159,plain,
    ( spl5_10
    | spl5_132
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f1149,f672,f1157,f113])).

fof(f1157,plain,
    ( spl5_132
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X5,sK3)
        | r1_tsep_1(sK1,X5)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f1149,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(sK1,X5)
        | ~ m1_pre_topc(X5,sK3)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_85 ),
    inference(resolution,[],[f673,f50])).

fof(f1155,plain,
    ( ~ spl5_13
    | spl5_131
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_9
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f1147,f672,f108,f148,f143,f138,f1153,f128])).

fof(f1147,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(sK1,X1)
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl5_9
    | ~ spl5_85 ),
    inference(resolution,[],[f673,f110])).

fof(f1139,plain,
    ( spl5_8
    | spl5_130
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f1126,f474,f1137,f103])).

fof(f1137,plain,
    ( spl5_130
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(X7,sK4)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f474,plain,
    ( spl5_64
  <=> ! [X5,X4] :
        ( r1_tsep_1(X4,sK4)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(sK4,X5)
        | ~ m1_pre_topc(sK1,X5)
        | ~ m1_pre_topc(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f1126,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(X7,sK4)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_64 ),
    inference(resolution,[],[f475,f167])).

fof(f475,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | r1_tsep_1(X4,sK4)
        | ~ m1_pre_topc(sK1,X5)
        | ~ m1_pre_topc(X4,sK1) )
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f474])).

fof(f1135,plain,
    ( spl5_8
    | spl5_129
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f1125,f474,f1133,f103])).

fof(f1133,plain,
    ( spl5_129
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(X4,sK4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f1125,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(X4,sK4)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_64 ),
    inference(resolution,[],[f475,f50])).

fof(f1131,plain,
    ( ~ spl5_13
    | spl5_128
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_7
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f1123,f474,f98,f148,f143,f138,f1129,f128])).

fof(f1129,plain,
    ( spl5_128
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f1123,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl5_7
    | ~ spl5_64 ),
    inference(resolution,[],[f475,f100])).

fof(f1065,plain,
    ( spl5_10
    | spl5_12
    | spl5_127
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1049,f909,f1063,f123,f113])).

fof(f1049,plain,
    ( ! [X6,X7] :
        ( r1_tsep_1(X6,sK2)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(sK2,X7)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,X7)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X6,X7)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl5_110 ),
    inference(resolution,[],[f911,f58])).

fof(f911,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f909])).

fof(f1061,plain,
    ( spl5_10
    | spl5_12
    | spl5_126
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1048,f909,f1059,f123,f113])).

fof(f1048,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(sK2,X4)
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK2,X5)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_110 ),
    inference(resolution,[],[f911,f59])).

fof(f1057,plain,
    ( spl5_12
    | spl5_10
    | spl5_125
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1047,f909,f1055,f113,f123])).

fof(f1047,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X3)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_110 ),
    inference(resolution,[],[f911,f60])).

fof(f1053,plain,
    ( spl5_12
    | spl5_10
    | spl5_124
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1046,f909,f1051,f113,f123])).

fof(f1046,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_110 ),
    inference(resolution,[],[f911,f61])).

fof(f1041,plain,
    ( spl5_8
    | spl5_12
    | spl5_123
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1034,f79,f1039,f123,f103])).

fof(f79,plain,
    ( spl5_3
  <=> r1_tsep_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1034,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f81,f61])).

fof(f81,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f1029,plain,
    ( spl5_18
    | spl5_122
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1015,f484,f1027,f174])).

fof(f1027,plain,
    ( spl5_122
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X7,sK3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f484,plain,
    ( spl5_65
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK3)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f1015,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,sK3)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_65 ),
    inference(resolution,[],[f485,f167])).

fof(f485,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f484])).

fof(f1025,plain,
    ( spl5_18
    | spl5_121
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1014,f484,f1023,f174])).

fof(f1023,plain,
    ( spl5_121
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X4,sK3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f1014,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,sK3)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_65 ),
    inference(resolution,[],[f485,f50])).

fof(f1021,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_9
    | spl5_120
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1017,f484,f148,f143,f138,f1019,f108,f98,f103,f118,f123])).

fof(f1019,plain,
    ( spl5_120
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f1017,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_65 ),
    inference(duplicate_literal_removal,[],[f1012])).

fof(f1012,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_65 ),
    inference(resolution,[],[f485,f68])).

fof(f978,plain,
    ( spl5_14
    | spl5_10
    | spl5_119
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f956,f617,f976,f113,f133])).

fof(f617,plain,
    ( spl5_80
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f956,plain,
    ( ! [X12,X11] :
        ( r1_tsep_1(sK3,X11)
        | ~ m1_pre_topc(X11,sK1)
        | ~ m1_pre_topc(sK3,X12)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X12)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X11,X12)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) )
    | ~ spl5_80 ),
    inference(resolution,[],[f61,f619])).

fof(f619,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f617])).

fof(f974,plain,
    ( spl5_18
    | spl5_10
    | spl5_118
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f955,f396,f972,f113,f174])).

fof(f955,plain,
    ( ! [X10,X9] :
        ( r1_tsep_1(sK3,X9)
        | ~ m1_pre_topc(X9,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X10)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X9,X10)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl5_50 ),
    inference(resolution,[],[f61,f398])).

fof(f398,plain,
    ( r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f396])).

fof(f970,plain,
    ( spl5_18
    | spl5_14
    | spl5_117
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f954,f391,f968,f133,f174])).

fof(f391,plain,
    ( spl5_49
  <=> r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f954,plain,
    ( ! [X8,X7] :
        ( r1_tsep_1(sK1,X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X8)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_49 ),
    inference(resolution,[],[f61,f393])).

fof(f393,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f391])).

fof(f966,plain,
    ( spl5_8
    | spl5_14
    | spl5_77
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f953,f437,f594,f133,f103])).

fof(f594,plain,
    ( spl5_77
  <=> ! [X3,X2] :
        ( r1_tsep_1(sK1,X2)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ m1_pre_topc(X2,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f953,plain,
    ( ! [X6,X5] :
        ( r1_tsep_1(sK1,X5)
        | ~ m1_pre_topc(X5,sK4)
        | ~ m1_pre_topc(sK1,X6)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK4,X6)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X5,X6)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_58 ),
    inference(resolution,[],[f61,f439])).

fof(f439,plain,
    ( r1_tsep_1(sK1,sK4)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f437])).

fof(f965,plain,
    ( spl5_19
    | spl5_18
    | spl5_116
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f952,f83,f963,f174,f178])).

fof(f952,plain,
    ( ! [X4,X3] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X4)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X3,X4)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f85])).

fof(f961,plain,
    ( spl5_18
    | spl5_115
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f957,f644,f959,f174])).

fof(f957,plain,
    ( ! [X2,X0,X1] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_81 ),
    inference(duplicate_literal_removal,[],[f951])).

fof(f951,plain,
    ( ! [X2,X0,X1] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_81 ),
    inference(resolution,[],[f61,f645])).

fof(f947,plain,
    ( spl5_14
    | ~ spl5_112
    | spl5_114
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f934,f803,f945,f936,f133])).

fof(f936,plain,
    ( spl5_112
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f945,plain,
    ( spl5_114
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK1,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK1,X2,X3),sK0)
        | r1_tsep_1(sK4,k2_tsep_1(sK1,X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f803,plain,
    ( spl5_96
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f934,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK1,X2,X3))
        | r1_tsep_1(sK4,k2_tsep_1(sK1,X2,X3))
        | ~ m1_pre_topc(k2_tsep_1(sK1,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_96 ),
    inference(resolution,[],[f804,f68])).

fof(f804,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f803])).

fof(f943,plain,
    ( spl5_14
    | ~ spl5_112
    | spl5_113
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f933,f803,f941,f936,f133])).

fof(f941,plain,
    ( spl5_113
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK1,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(k1_tsep_1(sK1,X0,X1),sK0)
        | r1_tsep_1(sK4,k1_tsep_1(sK1,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f933,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK1,X0,X1))
        | r1_tsep_1(sK4,k1_tsep_1(sK1,X0,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK1,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_96 ),
    inference(resolution,[],[f804,f65])).

fof(f939,plain,
    ( ~ spl5_112
    | ~ spl5_13
    | spl5_2
    | spl5_14
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f932,f803,f133,f74,f128,f936])).

fof(f932,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_96 ),
    inference(resolution,[],[f804,f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f927,plain,
    ( ~ spl5_9
    | spl5_111
    | spl5_10
    | ~ spl5_5
    | ~ spl5_93 ),
    inference(avatar_split_clause,[],[f922,f781,f88,f113,f924,f108])).

fof(f781,plain,
    ( spl5_93
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f922,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK1,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl5_5
    | ~ spl5_93 ),
    inference(resolution,[],[f782,f90])).

fof(f782,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f781])).

fof(f912,plain,
    ( ~ spl5_9
    | spl5_110
    | spl5_10
    | ~ spl5_5
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f907,f745,f88,f113,f909,f108])).

fof(f745,plain,
    ( spl5_90
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f907,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl5_5
    | ~ spl5_90 ),
    inference(resolution,[],[f746,f90])).

fof(f746,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f745])).

fof(f895,plain,
    ( ~ spl5_22
    | spl5_19
    | ~ spl5_109
    | spl5_4
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f890,f644,f83,f892,f178,f200])).

fof(f892,plain,
    ( spl5_109
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f890,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK1)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl5_4
    | ~ spl5_81 ),
    inference(resolution,[],[f84,f645])).

fof(f84,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f877,plain,
    ( spl5_18
    | spl5_108
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f863,f456,f875,f174])).

fof(f875,plain,
    ( spl5_108
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f456,plain,
    ( spl5_61
  <=> ! [X5,X4] :
        ( r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | ~ m1_pre_topc(sK1,X5)
        | ~ m1_pre_topc(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f863,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_61 ),
    inference(resolution,[],[f457,f167])).

fof(f457,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X5)
        | ~ m1_pre_topc(X4,sK1) )
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f456])).

fof(f873,plain,
    ( spl5_18
    | spl5_107
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f862,f456,f871,f174])).

fof(f871,plain,
    ( spl5_107
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f862,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_61 ),
    inference(resolution,[],[f457,f50])).

fof(f869,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_13
    | spl5_106
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f865,f456,f148,f143,f138,f867,f128,f98,f103,f118,f123])).

fof(f865,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_61 ),
    inference(duplicate_literal_removal,[],[f860])).

fof(f860,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_61 ),
    inference(resolution,[],[f457,f68])).

fof(f847,plain,
    ( spl5_10
    | spl5_105
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f818,f668,f845,f113])).

fof(f845,plain,
    ( spl5_105
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_pre_topc(X8,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(X8,sK3)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f818,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(k1_tsep_1(X6,X7,sK3))
        | ~ v2_pre_topc(k1_tsep_1(X6,X7,sK3))
        | ~ l1_pre_topc(k1_tsep_1(X6,X7,sK3))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3))
        | r1_tsep_1(X8,sK3)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3))
        | ~ m1_pre_topc(X8,sK1)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl5_84 ),
    inference(resolution,[],[f669,f167])).

fof(f669,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f668])).

fof(f843,plain,
    ( spl5_10
    | spl5_104
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f817,f668,f841,f113])).

fof(f841,plain,
    ( spl5_104
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X5,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(X5,sK3)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f817,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(k1_tsep_1(X3,sK3,X4))
        | ~ v2_pre_topc(k1_tsep_1(X3,sK3,X4))
        | ~ l1_pre_topc(k1_tsep_1(X3,sK3,X4))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4))
        | r1_tsep_1(X5,sK3)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4))
        | ~ m1_pre_topc(X5,sK1)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_84 ),
    inference(resolution,[],[f669,f50])).

fof(f839,plain,
    ( ~ spl5_100
    | spl5_101
    | ~ spl5_102
    | ~ spl5_103
    | spl5_10
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f819,f668,f113,f836,f832,f829,f825])).

fof(f825,plain,
    ( spl5_100
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f829,plain,
    ( spl5_101
  <=> ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK1)
        | r1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f836,plain,
    ( spl5_103
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f819,plain,
    ( ! [X2] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK3)
        | r1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(sK1,sK3)
        | ~ m1_pre_topc(X2,sK1) )
    | ~ spl5_84 ),
    inference(duplicate_literal_removal,[],[f816])).

fof(f816,plain,
    ( ! [X2] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK3)
        | r1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(sK1,sK3)
        | ~ m1_pre_topc(X2,sK1)
        | ~ l1_pre_topc(sK3) )
    | ~ spl5_84 ),
    inference(resolution,[],[f669,f49])).

fof(f823,plain,
    ( ~ spl5_13
    | spl5_99
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_9
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f815,f668,f108,f148,f143,f138,f821,f128])).

fof(f821,plain,
    ( spl5_99
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | r1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f815,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl5_9
    | ~ spl5_84 ),
    inference(resolution,[],[f669,f110])).

fof(f813,plain,
    ( spl5_8
    | spl5_98
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f800,f470,f811,f103])).

fof(f811,plain,
    ( spl5_98
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(sK4,X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f470,plain,
    ( spl5_63
  <=> ! [X3,X2] :
        ( r1_tsep_1(sK4,X2)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f800,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(sK4,X7)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_63 ),
    inference(resolution,[],[f471,f167])).

fof(f471,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X2,sK1) )
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f470])).

fof(f809,plain,
    ( spl5_8
    | spl5_97
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f799,f470,f807,f103])).

fof(f807,plain,
    ( spl5_97
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(sK4,X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f799,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(sK4,X4)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_63 ),
    inference(resolution,[],[f471,f50])).

fof(f805,plain,
    ( ~ spl5_13
    | spl5_96
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_7
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f797,f470,f98,f148,f143,f138,f803,f128])).

fof(f797,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl5_7
    | ~ spl5_63 ),
    inference(resolution,[],[f471,f100])).

fof(f791,plain,
    ( spl5_8
    | spl5_95
    | ~ spl5_77 ),
    inference(avatar_split_clause,[],[f778,f594,f789,f103])).

fof(f789,plain,
    ( spl5_95
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK4)
        | r1_tsep_1(sK1,X7)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f778,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(sK1,X7)
        | ~ m1_pre_topc(X7,sK4)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_77 ),
    inference(resolution,[],[f595,f167])).

fof(f595,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK1,X3)
        | r1_tsep_1(sK1,X2)
        | ~ m1_pre_topc(X2,sK4) )
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f594])).

fof(f787,plain,
    ( spl5_8
    | spl5_94
    | ~ spl5_77 ),
    inference(avatar_split_clause,[],[f777,f594,f785,f103])).

fof(f785,plain,
    ( spl5_94
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK4)
        | r1_tsep_1(sK1,X4)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f777,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(sK1,X4)
        | ~ m1_pre_topc(X4,sK4)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_77 ),
    inference(resolution,[],[f595,f50])).

fof(f783,plain,
    ( ~ spl5_13
    | spl5_93
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_7
    | ~ spl5_77 ),
    inference(avatar_split_clause,[],[f775,f594,f98,f148,f143,f138,f781,f128])).

fof(f775,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl5_7
    | ~ spl5_77 ),
    inference(resolution,[],[f595,f100])).

fof(f755,plain,
    ( spl5_8
    | spl5_92
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f742,f308,f753,f103])).

fof(f753,plain,
    ( spl5_92
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK4)
        | r1_tsep_1(X7,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f308,plain,
    ( spl5_38
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK2)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f742,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(X7,sK2)
        | ~ m1_pre_topc(X7,sK4)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_38 ),
    inference(resolution,[],[f309,f167])).

fof(f309,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f308])).

fof(f751,plain,
    ( spl5_8
    | spl5_91
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f741,f308,f749,f103])).

fof(f749,plain,
    ( spl5_91
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK4)
        | r1_tsep_1(X4,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f741,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(X4,sK2)
        | ~ m1_pre_topc(X4,sK4)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_38 ),
    inference(resolution,[],[f309,f50])).

fof(f747,plain,
    ( ~ spl5_11
    | spl5_90
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_7
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f739,f308,f98,f148,f143,f138,f745,f118])).

fof(f739,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl5_7
    | ~ spl5_38 ),
    inference(resolution,[],[f309,f100])).

fof(f704,plain,
    ( spl5_18
    | spl5_89
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f690,f644,f702,f174])).

fof(f690,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(X6,sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | r1_tsep_1(X7,X6)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_81 ),
    inference(duplicate_literal_removal,[],[f689])).

fof(f689,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(X6,sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | r1_tsep_1(X7,X6)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl5_81 ),
    inference(resolution,[],[f645,f58])).

fof(f700,plain,
    ( spl5_18
    | spl5_88
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f691,f644,f698,f174])).

fof(f691,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(X3,X4)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_81 ),
    inference(duplicate_literal_removal,[],[f688])).

fof(f688,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(X3,X4)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_81 ),
    inference(resolution,[],[f645,f59])).

fof(f696,plain,
    ( spl5_18
    | spl5_87
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f692,f644,f694,f174])).

fof(f692,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_81 ),
    inference(duplicate_literal_removal,[],[f687])).

fof(f687,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_81 ),
    inference(resolution,[],[f645,f60])).

fof(f680,plain,
    ( spl5_14
    | spl5_8
    | spl5_64
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f655,f74,f474,f103,f133])).

fof(f655,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f75,f60])).

fof(f75,plain,
    ( r1_tsep_1(sK4,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f679,plain,
    ( spl5_8
    | spl5_14
    | spl5_62
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f657,f74,f466,f133,f103])).

fof(f466,plain,
    ( spl5_62
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f657,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(X4,sK1)
        | ~ m1_pre_topc(X4,sK4)
        | ~ m1_pre_topc(sK1,X5)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_2 ),
    inference(resolution,[],[f75,f58])).

fof(f678,plain,
    ( spl5_10
    | spl5_14
    | spl5_86
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f666,f617,f676,f133,f113])).

fof(f666,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(X4,sK1)
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK1,X5)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_80 ),
    inference(resolution,[],[f619,f58])).

fof(f674,plain,
    ( spl5_10
    | spl5_14
    | spl5_85
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f665,f617,f672,f133,f113])).

fof(f665,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(sK1,X2)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_80 ),
    inference(resolution,[],[f619,f59])).

fof(f670,plain,
    ( spl5_14
    | spl5_10
    | spl5_84
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f664,f617,f668,f113,f133])).

fof(f664,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_80 ),
    inference(resolution,[],[f619,f60])).

fof(f654,plain,
    ( spl5_18
    | spl5_83
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f640,f452,f652,f174])).

fof(f652,plain,
    ( spl5_83
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f452,plain,
    ( spl5_60
  <=> ! [X3,X2] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f640,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,sK1)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_60 ),
    inference(resolution,[],[f453,f167])).

fof(f453,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X2,sK1) )
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f452])).

fof(f650,plain,
    ( spl5_18
    | spl5_82
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f639,f452,f648,f174])).

fof(f648,plain,
    ( spl5_82
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f639,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_60 ),
    inference(resolution,[],[f453,f50])).

fof(f646,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_13
    | spl5_81
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f642,f452,f148,f143,f138,f644,f128,f98,f103,f118,f123])).

fof(f642,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_60 ),
    inference(duplicate_literal_removal,[],[f637])).

fof(f637,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_60 ),
    inference(resolution,[],[f453,f68])).

fof(f620,plain,
    ( ~ spl5_9
    | spl5_80
    | spl5_10
    | ~ spl5_5
    | ~ spl5_71 ),
    inference(avatar_split_clause,[],[f606,f546,f88,f113,f617,f108])).

fof(f546,plain,
    ( spl5_71
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f606,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl5_5
    | ~ spl5_71 ),
    inference(resolution,[],[f547,f90])).

fof(f547,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f546])).

fof(f615,plain,
    ( spl5_8
    | ~ spl5_45
    | spl5_79
    | ~ spl5_71 ),
    inference(avatar_split_clause,[],[f605,f546,f613,f364,f103])).

fof(f364,plain,
    ( spl5_45
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f613,plain,
    ( spl5_79
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK4,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK4)
        | ~ m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(sK4,X2,X3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f605,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK4,X2,X3))
        | r1_tsep_1(k2_tsep_1(sK4,X2,X3),sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK4)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl5_71 ),
    inference(resolution,[],[f547,f68])).

fof(f611,plain,
    ( spl5_8
    | ~ spl5_45
    | spl5_78
    | ~ spl5_71 ),
    inference(avatar_split_clause,[],[f604,f546,f609,f364,f103])).

fof(f609,plain,
    ( spl5_78
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK4,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | ~ m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(sK4,X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f604,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK4,X0,X1))
        | r1_tsep_1(k1_tsep_1(sK4,X0,X1),sK1)
        | ~ m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl5_71 ),
    inference(resolution,[],[f547,f65])).

fof(f607,plain,
    ( ~ spl5_45
    | ~ spl5_7
    | spl5_2
    | spl5_8
    | ~ spl5_71 ),
    inference(avatar_split_clause,[],[f603,f546,f103,f74,f98,f364])).

fof(f603,plain,
    ( v2_struct_0(sK4)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK4)
    | ~ spl5_71 ),
    inference(resolution,[],[f547,f49])).

fof(f596,plain,
    ( spl5_8
    | spl5_14
    | spl5_77
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f591,f74,f594,f133,f103])).

fof(f591,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(sK1,X2)
        | ~ m1_pre_topc(X2,sK4)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f75,f59])).

fof(f589,plain,
    ( ~ spl5_13
    | spl5_2
    | spl5_14
    | ~ spl5_6
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f588,f516,f93,f133,f74,f128])).

fof(f516,plain,
    ( spl5_68
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f588,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl5_6
    | ~ spl5_68 ),
    inference(resolution,[],[f517,f95])).

fof(f95,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f516])).

fof(f574,plain,
    ( spl5_18
    | spl5_76
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f560,f448,f572,f174])).

fof(f572,plain,
    ( spl5_76
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X7,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f448,plain,
    ( spl5_59
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f560,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,sK1)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_59 ),
    inference(resolution,[],[f449,f167])).

fof(f449,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f448])).

fof(f570,plain,
    ( spl5_18
    | spl5_75
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f559,f448,f568,f174])).

fof(f568,plain,
    ( spl5_75
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X4,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f559,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,sK1)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_59 ),
    inference(resolution,[],[f449,f50])).

fof(f566,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_13
    | spl5_74
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f562,f448,f148,f143,f138,f564,f128,f98,f103,f118,f123])).

fof(f564,plain,
    ( spl5_74
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f562,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_59 ),
    inference(duplicate_literal_removal,[],[f557])).

fof(f557,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_59 ),
    inference(resolution,[],[f449,f68])).

fof(f556,plain,
    ( spl5_8
    | spl5_73
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f543,f466,f554,f103])).

fof(f554,plain,
    ( spl5_73
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK4)
        | r1_tsep_1(X7,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f543,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(X7,sK1)
        | ~ m1_pre_topc(X7,sK4)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_62 ),
    inference(resolution,[],[f467,f167])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f466])).

fof(f552,plain,
    ( spl5_8
    | spl5_72
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f542,f466,f550,f103])).

fof(f550,plain,
    ( spl5_72
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK4)
        | r1_tsep_1(X4,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f542,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(X4,sK1)
        | ~ m1_pre_topc(X4,sK4)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_62 ),
    inference(resolution,[],[f467,f50])).

fof(f548,plain,
    ( ~ spl5_13
    | spl5_71
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_7
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f540,f466,f98,f148,f143,f138,f546,f128])).

fof(f540,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl5_7
    | ~ spl5_62 ),
    inference(resolution,[],[f467,f100])).

fof(f526,plain,
    ( spl5_8
    | spl5_70
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f513,f279,f524,f103])).

fof(f524,plain,
    ( spl5_70
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(sK4,X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f279,plain,
    ( spl5_36
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK4,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f513,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(sK4,X7)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(X7,sK2)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_36 ),
    inference(resolution,[],[f280,f167])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f279])).

fof(f522,plain,
    ( spl5_8
    | spl5_69
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f512,f279,f520,f103])).

fof(f520,plain,
    ( spl5_69
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(sK4,X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f512,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(sK4,X4)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(X4,sK2)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_36 ),
    inference(resolution,[],[f280,f50])).

fof(f518,plain,
    ( ~ spl5_11
    | spl5_68
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_7
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f510,f279,f98,f148,f143,f138,f516,f118])).

fof(f510,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl5_7
    | ~ spl5_36 ),
    inference(resolution,[],[f280,f100])).

fof(f494,plain,
    ( spl5_10
    | spl5_18
    | spl5_67
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f482,f396,f492,f174,f113])).

fof(f482,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_50 ),
    inference(resolution,[],[f398,f58])).

fof(f490,plain,
    ( spl5_10
    | spl5_18
    | spl5_66
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f481,f396,f488,f174,f113])).

fof(f481,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_50 ),
    inference(resolution,[],[f398,f59])).

fof(f486,plain,
    ( spl5_18
    | spl5_10
    | spl5_65
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f480,f396,f484,f113,f174])).

fof(f480,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_50 ),
    inference(resolution,[],[f398,f60])).

fof(f476,plain,
    ( spl5_14
    | spl5_8
    | spl5_64
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f464,f437,f474,f103,f133])).

fof(f464,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(X4,sK4)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK1,X5)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_58 ),
    inference(resolution,[],[f439,f58])).

fof(f472,plain,
    ( spl5_14
    | spl5_8
    | spl5_63
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f463,f437,f470,f103,f133])).

fof(f463,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_58 ),
    inference(resolution,[],[f439,f59])).

fof(f468,plain,
    ( spl5_8
    | spl5_14
    | spl5_62
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f462,f437,f466,f133,f103])).

fof(f462,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_58 ),
    inference(resolution,[],[f439,f60])).

fof(f458,plain,
    ( spl5_14
    | spl5_18
    | spl5_61
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f446,f391,f456,f174,f133])).

fof(f446,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X5)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_49 ),
    inference(resolution,[],[f393,f58])).

fof(f454,plain,
    ( spl5_14
    | spl5_18
    | spl5_60
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f445,f391,f452,f174,f133])).

fof(f445,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_49 ),
    inference(resolution,[],[f393,f59])).

fof(f450,plain,
    ( spl5_18
    | spl5_14
    | spl5_59
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f444,f391,f448,f133,f174])).

fof(f444,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_49 ),
    inference(resolution,[],[f393,f60])).

fof(f440,plain,
    ( ~ spl5_13
    | spl5_58
    | spl5_14
    | ~ spl5_6
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f423,f353,f93,f133,f437,f128])).

fof(f353,plain,
    ( spl5_42
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f423,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK1,sK4)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl5_6
    | ~ spl5_42 ),
    inference(resolution,[],[f354,f95])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f353])).

fof(f435,plain,
    ( spl5_12
    | ~ spl5_55
    | spl5_57
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f422,f353,f433,f425,f123])).

fof(f425,plain,
    ( spl5_55
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f433,plain,
    ( spl5_57
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK2,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK2,X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(sK2,X2,X3),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f422,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK2,X2,X3))
        | r1_tsep_1(k2_tsep_1(sK2,X2,X3),sK4)
        | ~ m1_pre_topc(k2_tsep_1(sK2,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl5_42 ),
    inference(resolution,[],[f354,f68])).

fof(f431,plain,
    ( spl5_12
    | ~ spl5_55
    | spl5_56
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f421,f353,f429,f425,f123])).

fof(f429,plain,
    ( spl5_56
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK2,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(sK2,X0,X1),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f421,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK2,X0,X1))
        | r1_tsep_1(k1_tsep_1(sK2,X0,X1),sK4)
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl5_42 ),
    inference(resolution,[],[f354,f65])).

fof(f416,plain,
    ( spl5_19
    | ~ spl5_51
    | spl5_54
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f387,f333,f414,f401,f178])).

fof(f401,plain,
    ( spl5_51
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f414,plain,
    ( spl5_54
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f333,plain,
    ( spl5_39
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f387,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3))
        | r1_tsep_1(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),sK0)
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X2)
        | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl5_39 ),
    inference(resolution,[],[f334,f68])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f333])).

fof(f412,plain,
    ( spl5_19
    | ~ spl5_51
    | spl5_53
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f386,f333,f410,f401,f178])).

fof(f410,plain,
    ( spl5_53
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f386,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1))
        | r1_tsep_1(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),sK0)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl5_39 ),
    inference(resolution,[],[f334,f65])).

fof(f408,plain,
    ( ~ spl5_51
    | ~ spl5_22
    | spl5_52
    | spl5_19
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f385,f333,f178,f405,f200,f401])).

fof(f405,plain,
    ( spl5_52
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f385,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_39 ),
    inference(resolution,[],[f334,f49])).

fof(f399,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_14
    | ~ spl5_13
    | ~ spl5_9
    | spl5_50
    | spl5_10
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f388,f333,f113,f396,f108,f128,f133,f138,f143,f148])).

fof(f388,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_39 ),
    inference(duplicate_literal_removal,[],[f384])).

fof(f384,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_39 ),
    inference(resolution,[],[f334,f167])).

fof(f394,plain,
    ( spl5_17
    | ~ spl5_16
    | ~ spl5_15
    | spl5_10
    | ~ spl5_9
    | ~ spl5_13
    | spl5_49
    | spl5_14
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f389,f333,f133,f391,f128,f108,f113,f138,f143,f148])).

fof(f389,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_39 ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_39 ),
    inference(resolution,[],[f334,f50])).

fof(f379,plain,
    ( spl5_8
    | spl5_48
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f350,f187,f377,f103])).

fof(f377,plain,
    ( spl5_48
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(X7,sK4)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f187,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK4)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f350,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,sK4))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4))
        | r1_tsep_1(X7,sK4)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4))
        | ~ m1_pre_topc(X7,sK2)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK4,X5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_21 ),
    inference(resolution,[],[f188,f167])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f375,plain,
    ( spl5_8
    | spl5_47
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f349,f187,f373,f103])).

fof(f373,plain,
    ( spl5_47
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(X4,sK4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f349,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,sK4,X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,sK4,X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,sK4,X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3))
        | r1_tsep_1(X4,sK4)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3))
        | ~ m1_pre_topc(X4,sK2)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK4,X2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_21 ),
    inference(resolution,[],[f188,f50])).

fof(f371,plain,
    ( ~ spl5_43
    | spl5_44
    | ~ spl5_45
    | ~ spl5_46
    | spl5_8
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f351,f187,f103,f368,f364,f361,f357])).

fof(f357,plain,
    ( spl5_43
  <=> m1_pre_topc(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f361,plain,
    ( spl5_44
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(X1,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f368,plain,
    ( spl5_46
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f351,plain,
    ( ! [X1] :
        ( v2_struct_0(sK4)
        | ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(sK2,sK4)
        | ~ m1_pre_topc(X1,sK2) )
    | ~ spl5_21 ),
    inference(duplicate_literal_removal,[],[f348])).

fof(f348,plain,
    ( ! [X1] :
        ( v2_struct_0(sK4)
        | ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | r1_tsep_1(X1,sK4)
        | ~ m1_pre_topc(sK2,sK4)
        | ~ m1_pre_topc(X1,sK2)
        | ~ l1_pre_topc(sK4) )
    | ~ spl5_21 ),
    inference(resolution,[],[f188,f49])).

fof(f355,plain,
    ( ~ spl5_11
    | spl5_42
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f347,f187,f98,f148,f143,f138,f353,f118])).

fof(f347,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(resolution,[],[f188,f100])).

fof(f343,plain,
    ( spl5_18
    | spl5_41
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f329,f301,f341,f174])).

fof(f341,plain,
    ( spl5_41
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f301,plain,
    ( spl5_37
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f329,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_37 ),
    inference(resolution,[],[f302,f167])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f301])).

fof(f339,plain,
    ( spl5_18
    | spl5_40
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f328,f301,f337,f174])).

fof(f337,plain,
    ( spl5_40
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f328,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_37 ),
    inference(resolution,[],[f302,f50])).

fof(f335,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_22
    | spl5_39
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f331,f301,f148,f143,f138,f333,f200,f98,f103,f118,f123])).

fof(f331,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_37 ),
    inference(duplicate_literal_removal,[],[f326])).

fof(f326,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_37 ),
    inference(resolution,[],[f302,f68])).

fof(f310,plain,
    ( spl5_8
    | spl5_12
    | spl5_38
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f304,f79,f308,f123,f103])).

fof(f304,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f81,f60])).

fof(f303,plain,
    ( spl5_19
    | spl5_18
    | spl5_37
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f299,f83,f301,f174,f178])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f60,f85])).

fof(f281,plain,
    ( spl5_12
    | spl5_8
    | spl5_36
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f276,f79,f279,f103,f123])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f81,f59])).

fof(f275,plain,
    ( spl5_18
    | spl5_35
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f261,f235,f273,f174])).

fof(f273,plain,
    ( spl5_35
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X7)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f235,plain,
    ( spl5_30
  <=> ! [X1,X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f261,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_30 ),
    inference(resolution,[],[f236,f167])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f235])).

fof(f271,plain,
    ( spl5_18
    | spl5_34
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f260,f235,f269,f174])).

fof(f269,plain,
    ( spl5_34
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X4)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f260,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X4)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_30 ),
    inference(resolution,[],[f236,f50])).

fof(f267,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_22
    | spl5_33
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f263,f235,f148,f143,f138,f265,f200,f98,f103,f118,f123])).

fof(f265,plain,
    ( spl5_33
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f263,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_30 ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_30 ),
    inference(resolution,[],[f236,f68])).

fof(f251,plain,
    ( spl5_18
    | ~ spl5_26
    | spl5_32
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f243,f204,f249,f215,f174])).

fof(f215,plain,
    ( spl5_26
  <=> l1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f249,plain,
    ( spl5_32
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f204,plain,
    ( spl5_23
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f243,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3))
        | r1_tsep_1(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),sK0)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X2)
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_23 ),
    inference(resolution,[],[f205,f68])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f204])).

fof(f247,plain,
    ( spl5_18
    | ~ spl5_26
    | spl5_31
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f242,f204,f245,f215,f174])).

fof(f245,plain,
    ( spl5_31
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1))
        | r1_tsep_1(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),sK0)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_23 ),
    inference(resolution,[],[f205,f65])).

fof(f240,plain,
    ( spl5_17
    | ~ spl5_15
    | spl5_14
    | ~ spl5_13
    | spl5_10
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f239,f178,f108,f113,f128,f133,f138,f148])).

fof(f239,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_19 ),
    inference(resolution,[],[f180,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f180,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f238,plain,
    ( spl5_18
    | spl5_19
    | spl5_20
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f192,f83,f182,f178,f174])).

fof(f182,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f85,f58])).

fof(f237,plain,
    ( spl5_18
    | spl5_19
    | spl5_30
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f233,f83,f235,f178,f174])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f59,f85])).

fof(f232,plain,
    ( spl5_17
    | ~ spl5_15
    | spl5_14
    | ~ spl5_13
    | spl5_10
    | ~ spl5_9
    | spl5_22 ),
    inference(avatar_split_clause,[],[f231,f200,f108,f113,f128,f133,f138,f148])).

fof(f231,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_22 ),
    inference(resolution,[],[f202,f65])).

fof(f202,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f230,plain,
    ( spl5_18
    | spl5_29
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f196,f182,f228,f174])).

fof(f228,plain,
    ( spl5_29
  <=> ! [X5,X7,X6] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X7,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f196,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X7,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl5_20 ),
    inference(resolution,[],[f183,f167])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f226,plain,
    ( spl5_18
    | spl5_28
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f195,f182,f224,f174])).

fof(f224,plain,
    ( spl5_28
  <=> ! [X3,X2,X4] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X4,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f195,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3))
        | r1_tsep_1(X4,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_20 ),
    inference(resolution,[],[f183,f50])).

fof(f222,plain,
    ( ~ spl5_24
    | spl5_25
    | ~ spl5_26
    | ~ spl5_27
    | spl5_18
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f197,f182,f174,f219,f215,f212,f208])).

fof(f208,plain,
    ( spl5_24
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f212,plain,
    ( spl5_25
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | r1_tsep_1(X1,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f219,plain,
    ( spl5_27
  <=> v2_pre_topc(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f197,plain,
    ( ! [X1] :
        ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ v2_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X1,k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl5_20 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ! [X1] :
        ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ v2_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X1,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl5_20 ),
    inference(resolution,[],[f183,f49])).

fof(f206,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_22
    | spl5_23
    | ~ spl5_15
    | ~ spl5_16
    | spl5_17
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f198,f182,f148,f143,f138,f204,f200,f98,f103,f118,f123])).

fof(f198,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl5_20 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_20 ),
    inference(resolution,[],[f183,f68])).

fof(f191,plain,
    ( spl5_17
    | ~ spl5_15
    | spl5_12
    | ~ spl5_11
    | spl5_8
    | ~ spl5_7
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f190,f174,f98,f103,f118,f123,f138,f148])).

fof(f190,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_18 ),
    inference(resolution,[],[f176,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f176,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f189,plain,
    ( spl5_12
    | spl5_8
    | spl5_21
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f185,f79,f187,f103,f123])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f81,f58])).

fof(f184,plain,
    ( spl5_18
    | spl5_19
    | spl5_20
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f172,f83,f182,f178,f174])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f58,f85])).

fof(f151,plain,(
    ~ spl5_17 ),
    inference(avatar_split_clause,[],[f34,f148])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r1_tsep_1(sK4,sK1)
      | ~ r1_tsep_1(sK2,sK3) )
    & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
      | r1_tsep_1(sK2,sK4) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f32,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tsep_1(X4,X1)
                          | ~ r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                          | r1_tsep_1(X2,X4) )
                        & m1_pre_topc(X3,X4)
                        & m1_pre_topc(X1,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tsep_1(X4,X1)
                      | ~ r1_tsep_1(X2,X3) )
                    & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                      | r1_tsep_1(X2,X4) )
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tsep_1(X4,sK1)
                    | ~ r1_tsep_1(X2,X3) )
                  & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3))
                    | r1_tsep_1(X2,X4) )
                  & m1_pre_topc(X3,X4)
                  & m1_pre_topc(sK1,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tsep_1(X4,sK1)
                  | ~ r1_tsep_1(X2,X3) )
                & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3))
                  | r1_tsep_1(X2,X4) )
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tsep_1(X4,sK1)
                | ~ r1_tsep_1(sK2,X3) )
              & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3))
                | r1_tsep_1(sK2,X4) )
              & m1_pre_topc(X3,X4)
              & m1_pre_topc(sK1,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_tsep_1(X4,sK1)
              | ~ r1_tsep_1(sK2,X3) )
            & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3))
              | r1_tsep_1(sK2,X4) )
            & m1_pre_topc(X3,X4)
            & m1_pre_topc(sK1,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ r1_tsep_1(X4,sK1)
            | ~ r1_tsep_1(sK2,sK3) )
          & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3))
            | r1_tsep_1(sK2,X4) )
          & m1_pre_topc(sK3,X4)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ( ~ r1_tsep_1(X4,sK1)
          | ~ r1_tsep_1(sK2,sK3) )
        & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3))
          | r1_tsep_1(sK2,X4) )
        & m1_pre_topc(sK3,X4)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ( ~ r1_tsep_1(sK4,sK1)
        | ~ r1_tsep_1(sK2,sK3) )
      & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(sK2,sK4) )
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => ( ( r1_tsep_1(X4,X1)
                              & r1_tsep_1(X2,X3) )
                            | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                              & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => ( ( r1_tsep_1(X4,X1)
                            & r1_tsep_1(X2,X3) )
                          | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                            & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tmap_1)).

fof(f146,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f35,f143])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f141,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f36,f138])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f136,plain,(
    ~ spl5_14 ),
    inference(avatar_split_clause,[],[f37,f133])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f38,f128])).

fof(f38,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f126,plain,(
    ~ spl5_12 ),
    inference(avatar_split_clause,[],[f39,f123])).

fof(f39,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f121,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f40,f118])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f116,plain,(
    ~ spl5_10 ),
    inference(avatar_split_clause,[],[f41,f113])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f42,f108])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f43,f103])).

fof(f43,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f44,f98])).

fof(f44,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f45,f93])).

fof(f45,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f47,f83,f79])).

fof(f47,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f74,f70])).

fof(f48,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.51  % (4710)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.23/0.51  % (4707)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.23/0.51  % (4709)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.51  % (4711)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.23/0.51  % (4708)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.23/0.52  % (4727)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.23/0.52  % (4706)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.23/0.52  % (4724)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.23/0.52  % (4726)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.23/0.52  % (4716)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.23/0.53  % (4715)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.23/0.53  % (4714)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.23/0.53  % (4719)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.23/0.53  % (4717)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.23/0.53  % (4723)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.23/0.53  % (4728)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.23/0.53  % (4720)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.23/0.53  % (4725)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.23/0.53  % (4722)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.23/0.54  % (4718)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.23/0.54  % (4721)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.30/0.54  % (4705)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.30/0.54  % (4712)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.55  % (4713)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.53/0.59  % (4721)Refutation not found, incomplete strategy% (4721)------------------------------
% 1.53/0.59  % (4721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (4721)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (4721)Memory used [KB]: 2046
% 1.53/0.59  % (4721)Time elapsed: 0.180 s
% 1.53/0.59  % (4721)------------------------------
% 1.53/0.59  % (4721)------------------------------
% 2.98/0.77  % (4712)Refutation not found, incomplete strategy% (4712)------------------------------
% 2.98/0.77  % (4712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.77  % (4712)Termination reason: Refutation not found, incomplete strategy
% 2.98/0.77  
% 2.98/0.77  % (4712)Memory used [KB]: 8443
% 2.98/0.77  % (4712)Time elapsed: 0.332 s
% 2.98/0.77  % (4712)------------------------------
% 2.98/0.77  % (4712)------------------------------
% 3.48/0.82  % (4715)Refutation not found, incomplete strategy% (4715)------------------------------
% 3.48/0.82  % (4715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.82  % (4715)Termination reason: Refutation not found, incomplete strategy
% 3.48/0.82  
% 3.48/0.82  % (4715)Memory used [KB]: 12409
% 3.48/0.82  % (4715)Time elapsed: 0.404 s
% 3.48/0.82  % (4715)------------------------------
% 3.48/0.82  % (4715)------------------------------
% 3.92/0.92  % (4717)Time limit reached!
% 3.92/0.92  % (4717)------------------------------
% 3.92/0.92  % (4717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.92  % (4717)Termination reason: Time limit
% 3.92/0.92  
% 3.92/0.92  % (4717)Memory used [KB]: 15351
% 3.92/0.92  % (4717)Time elapsed: 0.507 s
% 3.92/0.92  % (4717)------------------------------
% 3.92/0.92  % (4717)------------------------------
% 3.92/0.94  % (4709)Refutation found. Thanks to Tanya!
% 3.92/0.94  % SZS status Theorem for theBenchmark
% 3.92/0.94  % SZS output start Proof for theBenchmark
% 3.92/0.94  fof(f2180,plain,(
% 3.92/0.94    $false),
% 3.92/0.94    inference(avatar_sat_refutation,[],[f77,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f184,f189,f191,f206,f222,f226,f230,f232,f237,f238,f240,f247,f251,f267,f271,f275,f281,f303,f310,f335,f339,f343,f355,f371,f375,f379,f394,f399,f408,f412,f416,f431,f435,f440,f450,f454,f458,f468,f472,f476,f486,f490,f494,f518,f522,f526,f548,f552,f556,f566,f570,f574,f589,f596,f607,f611,f615,f620,f646,f650,f654,f670,f674,f678,f679,f680,f696,f700,f704,f747,f751,f755,f783,f787,f791,f805,f809,f813,f823,f839,f843,f847,f869,f873,f877,f895,f912,f927,f939,f943,f947,f961,f965,f966,f970,f974,f978,f1021,f1025,f1029,f1041,f1053,f1057,f1061,f1065,f1131,f1135,f1139,f1155,f1159,f1163,f1164,f1165,f1166,f1167,f1195,f1199,f1203,f1233,f1264,f1268,f1297,f1301,f1305,f1325,f1329,f1333,f1337,f1348,f1393,f1397,f1401,f1414,f1418,f1422,f1447,f1451,f1455,f1473,f1477,f1481,f1494,f1498,f1502,f1533,f1537,f1541,f1553,f1558,f1576,f1580,f1584,f1596,f1600,f1604,f1608,f1626,f1635,f1636,f1645,f1649,f1653,f1657,f1694,f1698,f1702,f1715,f1719,f1723,f1736,f1740,f1744,f1758,f1772,f1776,f1780,f1794,f1798,f1802,f1806,f1810,f1824,f1828,f1832,f1845,f1855,f1859,f1863,f1876,f1880,f1884,f1910,f1914,f1918,f1922,f1931,f1940,f1941,f1945,f1949,f1953,f1957,f1998,f2002,f2006,f2010,f2011,f2015,f2019,f2023,f2027,f2055,f2059,f2063,f2077,f2081,f2085,f2099,f2103,f2107,f2120,f2124,f2128,f2154,f2158,f2162,f2163,f2167,f2171,f2175,f2179])).
% 3.92/0.94  fof(f2179,plain,(
% 3.92/0.94    spl5_18 | spl5_248 | ~spl5_106),
% 3.92/0.94    inference(avatar_split_clause,[],[f2142,f867,f2177,f174])).
% 3.92/0.94  fof(f174,plain,(
% 3.92/0.94    spl5_18 <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK4))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 3.92/0.94  fof(f2177,plain,(
% 3.92/0.94    spl5_248 <=> ! [X18,X17,X19] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | ~m1_pre_topc(k2_tsep_1(X19,X17,X18),sK0) | v2_struct_0(k2_tsep_1(X19,X17,X18)) | ~m1_pre_topc(k2_tsep_1(X19,X17,X18),sK1) | v2_struct_0(X19) | ~v2_pre_topc(X19) | ~l1_pre_topc(X19) | v2_struct_0(X18) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19) | v2_struct_0(X17) | ~m1_pre_topc(X17,X19) | r1_tsep_1(X18,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X18,X19))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_248])])).
% 3.92/0.94  fof(f867,plain,(
% 3.92/0.94    spl5_106 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).
% 3.92/0.94  fof(f2142,plain,(
% 3.92/0.94    ( ! [X19,X17,X18] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | r1_tsep_1(X18,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X17,X19) | v2_struct_0(X17) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X18,X19) | v2_struct_0(X18) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v2_struct_0(X19) | ~m1_pre_topc(k2_tsep_1(X19,X17,X18),sK1) | v2_struct_0(k2_tsep_1(X19,X17,X18)) | ~m1_pre_topc(k2_tsep_1(X19,X17,X18),sK0)) ) | ~spl5_106),
% 3.92/0.94    inference(resolution,[],[f57,f868])).
% 3.92/0.94  fof(f868,plain,(
% 3.92/0.94    ( ! [X0] : (r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_106),
% 3.92/0.94    inference(avatar_component_clause,[],[f867])).
% 3.92/0.94  fof(f57,plain,(
% 3.92/0.94    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f19])).
% 3.92/0.94  fof(f19,plain,(
% 3.92/0.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) | ~m1_pre_topc(X2,X3)) & ((~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.92/0.94    inference(flattening,[],[f18])).
% 3.92/0.94  fof(f18,plain,(
% 3.92/0.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((((~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) | ~m1_pre_topc(X2,X3)) & ((~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.92/0.94    inference(ennf_transformation,[],[f8])).
% 3.92/0.94  fof(f8,axiom,(
% 3.92/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 3.92/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).
% 3.92/0.94  fof(f2175,plain,(
% 3.92/0.94    spl5_18 | spl5_247 | ~spl5_153),
% 3.92/0.94    inference(avatar_split_clause,[],[f2141,f1445,f2173,f174])).
% 3.92/0.94  fof(f2173,plain,(
% 3.92/0.94    spl5_247 <=> ! [X16,X15,X14] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14) | ~m1_pre_topc(k2_tsep_1(X16,X14,X15),sK0) | v2_struct_0(k2_tsep_1(X16,X14,X15)) | ~m1_pre_topc(k2_tsep_1(X16,X14,X15),sK3) | v2_struct_0(X16) | ~v2_pre_topc(X16) | ~l1_pre_topc(X16) | v2_struct_0(X15) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16) | v2_struct_0(X14) | ~m1_pre_topc(X14,X16) | r1_tsep_1(X15,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X15,X16))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_247])])).
% 3.92/0.94  fof(f1445,plain,(
% 3.92/0.94    spl5_153 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).
% 3.92/0.94  fof(f2141,plain,(
% 3.92/0.94    ( ! [X14,X15,X16] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14) | r1_tsep_1(X15,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X14,X16) | v2_struct_0(X14) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X15,X16) | v2_struct_0(X15) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16) | v2_struct_0(X16) | ~m1_pre_topc(k2_tsep_1(X16,X14,X15),sK3) | v2_struct_0(k2_tsep_1(X16,X14,X15)) | ~m1_pre_topc(k2_tsep_1(X16,X14,X15),sK0)) ) | ~spl5_153),
% 3.92/0.94    inference(resolution,[],[f57,f1446])).
% 3.92/0.94  fof(f1446,plain,(
% 3.92/0.94    ( ! [X0] : (r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_153),
% 3.92/0.94    inference(avatar_component_clause,[],[f1445])).
% 3.92/0.94  fof(f2171,plain,(
% 3.92/0.94    spl5_18 | spl5_246 | ~spl5_167),
% 3.92/0.94    inference(avatar_split_clause,[],[f2140,f1574,f2169,f174])).
% 3.92/0.94  fof(f2169,plain,(
% 3.92/0.94    spl5_246 <=> ! [X11,X13,X10,X12] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(k2_tsep_1(X12,X10,X11),sK0) | ~m1_pre_topc(X13,sK1) | ~m1_pre_topc(X13,sK0) | v2_struct_0(k2_tsep_1(X12,X10,X11)) | ~m1_pre_topc(k2_tsep_1(X12,X10,X11),X13) | v2_struct_0(X13) | v2_struct_0(X12) | ~v2_pre_topc(X12) | ~l1_pre_topc(X12) | v2_struct_0(X11) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12) | v2_struct_0(X10) | ~m1_pre_topc(X10,X12) | r1_tsep_1(X11,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,X12))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_246])])).
% 3.92/0.94  fof(f1574,plain,(
% 3.92/0.94    spl5_167 <=> ! [X1,X0] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).
% 3.92/0.94  fof(f2140,plain,(
% 3.92/0.94    ( ! [X12,X10,X13,X11] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | r1_tsep_1(X11,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X10,X12) | v2_struct_0(X10) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,X12) | v2_struct_0(X11) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | v2_struct_0(X13) | ~m1_pre_topc(k2_tsep_1(X12,X10,X11),X13) | v2_struct_0(k2_tsep_1(X12,X10,X11)) | ~m1_pre_topc(X13,sK0) | ~m1_pre_topc(X13,sK1) | ~m1_pre_topc(k2_tsep_1(X12,X10,X11),sK0)) ) | ~spl5_167),
% 3.92/0.94    inference(resolution,[],[f57,f1575])).
% 3.92/0.94  fof(f1575,plain,(
% 3.92/0.94    ( ! [X0,X1] : (r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_167),
% 3.92/0.94    inference(avatar_component_clause,[],[f1574])).
% 3.92/0.94  fof(f2167,plain,(
% 3.92/0.94    spl5_18 | spl5_245 | ~spl5_200),
% 3.92/0.94    inference(avatar_split_clause,[],[f2139,f1822,f2165,f174])).
% 3.92/0.94  fof(f2165,plain,(
% 3.92/0.94    spl5_245 <=> ! [X9,X7,X8,X6] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6) | ~m1_pre_topc(k2_tsep_1(X8,X6,X7),sK0) | ~m1_pre_topc(X9,sK3) | ~m1_pre_topc(X9,sK0) | v2_struct_0(k2_tsep_1(X8,X6,X7)) | ~m1_pre_topc(k2_tsep_1(X8,X6,X7),X9) | v2_struct_0(X9) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(X7) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X6) | ~m1_pre_topc(X6,X8) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_245])])).
% 3.92/0.94  fof(f1822,plain,(
% 3.92/0.94    spl5_200 <=> ! [X1,X0] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).
% 3.92/0.94  fof(f2139,plain,(
% 3.92/0.94    ( ! [X6,X8,X7,X9] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X8) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(X8,X6,X7),X9) | v2_struct_0(k2_tsep_1(X8,X6,X7)) | ~m1_pre_topc(X9,sK0) | ~m1_pre_topc(X9,sK3) | ~m1_pre_topc(k2_tsep_1(X8,X6,X7),sK0)) ) | ~spl5_200),
% 3.92/0.94    inference(resolution,[],[f57,f1823])).
% 3.92/0.94  fof(f1823,plain,(
% 3.92/0.94    ( ! [X0,X1] : (r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_200),
% 3.92/0.94    inference(avatar_component_clause,[],[f1822])).
% 3.92/0.94  fof(f2163,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_8 | ~spl5_7 | spl5_14 | ~spl5_13 | spl5_12 | ~spl5_11 | spl5_2 | ~spl5_6 | ~spl5_165),
% 3.92/0.94    inference(avatar_split_clause,[],[f2137,f1550,f93,f74,f118,f123,f128,f133,f98,f103,f138,f143,f148])).
% 3.92/0.94  fof(f148,plain,(
% 3.92/0.94    spl5_17 <=> v2_struct_0(sK0)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 3.92/0.94  fof(f143,plain,(
% 3.92/0.94    spl5_16 <=> v2_pre_topc(sK0)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 3.92/0.94  fof(f138,plain,(
% 3.92/0.94    spl5_15 <=> l1_pre_topc(sK0)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 3.92/0.94  fof(f103,plain,(
% 3.92/0.94    spl5_8 <=> v2_struct_0(sK4)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.92/0.94  fof(f98,plain,(
% 3.92/0.94    spl5_7 <=> m1_pre_topc(sK4,sK0)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.92/0.94  fof(f133,plain,(
% 3.92/0.94    spl5_14 <=> v2_struct_0(sK1)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 3.92/0.94  fof(f128,plain,(
% 3.92/0.94    spl5_13 <=> m1_pre_topc(sK1,sK0)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.92/0.94  fof(f123,plain,(
% 3.92/0.94    spl5_12 <=> v2_struct_0(sK2)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.92/0.94  fof(f118,plain,(
% 3.92/0.94    spl5_11 <=> m1_pre_topc(sK2,sK0)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.92/0.94  fof(f74,plain,(
% 3.92/0.94    spl5_2 <=> r1_tsep_1(sK4,sK1)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.92/0.94  fof(f93,plain,(
% 3.92/0.94    spl5_6 <=> m1_pre_topc(sK1,sK2)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.92/0.94  fof(f1550,plain,(
% 3.92/0.94    spl5_165 <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).
% 3.92/0.94  fof(f2137,plain,(
% 3.92/0.94    ~m1_pre_topc(sK1,sK2) | r1_tsep_1(sK4,sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_165),
% 3.92/0.94    inference(resolution,[],[f57,f1552])).
% 3.92/0.94  fof(f1552,plain,(
% 3.92/0.94    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) | ~spl5_165),
% 3.92/0.94    inference(avatar_component_clause,[],[f1550])).
% 3.92/0.94  fof(f2162,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_244 | ~spl5_134),
% 3.92/0.94    inference(avatar_split_clause,[],[f2148,f1193,f2160,f118,f123,f98,f103,f138,f143,f148])).
% 3.92/0.94  fof(f2160,plain,(
% 3.92/0.94    spl5_244 <=> ! [X4] : (~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | r1_tsep_1(sK4,X4))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_244])])).
% 3.92/0.94  fof(f1193,plain,(
% 3.92/0.94    spl5_134 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).
% 3.92/0.94  fof(f2148,plain,(
% 3.92/0.94    ( ! [X4] : (~m1_pre_topc(X4,sK2) | r1_tsep_1(sK4,X4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X4,sK3)) ) | ~spl5_134),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f2134])).
% 3.92/0.94  fof(f2134,plain,(
% 3.92/0.94    ( ! [X4] : (~m1_pre_topc(X4,sK2) | r1_tsep_1(sK4,X4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0)) ) | ~spl5_134),
% 3.92/0.94    inference(resolution,[],[f57,f1194])).
% 3.92/0.94  fof(f1194,plain,(
% 3.92/0.94    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_134),
% 3.92/0.94    inference(avatar_component_clause,[],[f1193])).
% 3.92/0.94  fof(f2158,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_243 | ~spl5_188),
% 3.92/0.94    inference(avatar_split_clause,[],[f2149,f1734,f2156,f118,f123,f98,f103,f138,f143,f148])).
% 3.92/0.94  fof(f2156,plain,(
% 3.92/0.94    spl5_243 <=> ! [X3,X2] : (~m1_pre_topc(X2,sK2) | ~m1_pre_topc(X3,sK1) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,X3) | v2_struct_0(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(sK4,X2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_243])])).
% 3.92/0.94  fof(f1734,plain,(
% 3.92/0.94    spl5_188 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK1))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).
% 3.92/0.94  fof(f2149,plain,(
% 3.92/0.94    ( ! [X2,X3] : (~m1_pre_topc(X2,sK2) | r1_tsep_1(sK4,X2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X3,sK1)) ) | ~spl5_188),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f2133])).
% 3.92/0.94  fof(f2133,plain,(
% 3.92/0.94    ( ! [X2,X3] : (~m1_pre_topc(X2,sK2) | r1_tsep_1(sK4,X2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,sK1)) ) | ~spl5_188),
% 3.92/0.94    inference(resolution,[],[f57,f1735])).
% 3.92/0.94  fof(f1735,plain,(
% 3.92/0.94    ( ! [X0,X1] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK1)) ) | ~spl5_188),
% 3.92/0.94    inference(avatar_component_clause,[],[f1734])).
% 3.92/0.94  fof(f2154,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_242 | ~spl5_192),
% 3.92/0.94    inference(avatar_split_clause,[],[f2150,f1770,f2152,f118,f123,f98,f103,f138,f143,f148])).
% 3.92/0.94  fof(f2152,plain,(
% 3.92/0.94    spl5_242 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(sK4,X0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_242])])).
% 3.92/0.94  fof(f1770,plain,(
% 3.92/0.94    spl5_192 <=> ! [X1,X0] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).
% 3.92/0.94  fof(f2150,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3)) ) | ~spl5_192),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f2132])).
% 3.92/0.94  fof(f2132,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_192),
% 3.92/0.94    inference(resolution,[],[f57,f1771])).
% 3.92/0.94  fof(f1771,plain,(
% 3.92/0.94    ( ! [X0,X1] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_192),
% 3.92/0.94    inference(avatar_component_clause,[],[f1770])).
% 3.92/0.94  fof(f2128,plain,(
% 3.92/0.94    spl5_10 | spl5_241 | ~spl5_127),
% 3.92/0.94    inference(avatar_split_clause,[],[f2115,f1063,f2126,f113])).
% 3.92/0.94  fof(f113,plain,(
% 3.92/0.94    spl5_10 <=> v2_struct_0(sK3)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.92/0.94  fof(f2126,plain,(
% 3.92/0.94    spl5_241 <=> ! [X7,X8,X6] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X8,sK3) | r1_tsep_1(X8,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_241])])).
% 3.92/0.94  fof(f1063,plain,(
% 3.92/0.94    spl5_127 <=> ! [X7,X6] : (r1_tsep_1(X6,sK2) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(sK2,X7) | ~m1_pre_topc(sK3,X7) | ~m1_pre_topc(X6,sK3))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).
% 3.92/0.94  fof(f2115,plain,(
% 3.92/0.94    ( ! [X6,X8,X7] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(X8,sK2) | ~m1_pre_topc(X8,sK3) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_127),
% 3.92/0.94    inference(resolution,[],[f1064,f167])).
% 3.92/0.94  fof(f167,plain,(
% 3.92/0.94    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f152])).
% 3.92/0.94  fof(f152,plain,(
% 3.92/0.94    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(superposition,[],[f50,f62])).
% 3.92/0.94  fof(f62,plain,(
% 3.92/0.94    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f23])).
% 3.92/0.94  fof(f23,plain,(
% 3.92/0.94    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.92/0.94    inference(flattening,[],[f22])).
% 3.92/0.94  fof(f22,plain,(
% 3.92/0.94    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.92/0.94    inference(ennf_transformation,[],[f1])).
% 3.92/0.94  fof(f1,axiom,(
% 3.92/0.94    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 3.92/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).
% 3.92/0.94  fof(f50,plain,(
% 3.92/0.94    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f15])).
% 3.92/0.94  fof(f15,plain,(
% 3.92/0.94    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.92/0.94    inference(flattening,[],[f14])).
% 3.92/0.94  fof(f14,plain,(
% 3.92/0.94    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.92/0.94    inference(ennf_transformation,[],[f4])).
% 3.92/0.94  fof(f4,axiom,(
% 3.92/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.92/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).
% 3.92/0.94  fof(f1064,plain,(
% 3.92/0.94    ( ! [X6,X7] : (~m1_pre_topc(sK3,X7) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(sK2,X7) | r1_tsep_1(X6,sK2) | ~m1_pre_topc(X6,sK3)) ) | ~spl5_127),
% 3.92/0.94    inference(avatar_component_clause,[],[f1063])).
% 3.92/0.94  fof(f2124,plain,(
% 3.92/0.94    spl5_10 | spl5_240 | ~spl5_127),
% 3.92/0.94    inference(avatar_split_clause,[],[f2114,f1063,f2122,f113])).
% 3.92/0.94  fof(f2122,plain,(
% 3.92/0.94    spl5_240 <=> ! [X3,X5,X4] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X5,sK3) | r1_tsep_1(X5,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_240])])).
% 3.92/0.94  fof(f2114,plain,(
% 3.92/0.94    ( ! [X4,X5,X3] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(X5,sK2) | ~m1_pre_topc(X5,sK3) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_127),
% 3.92/0.94    inference(resolution,[],[f1064,f50])).
% 3.92/0.94  fof(f2120,plain,(
% 3.92/0.94    ~spl5_11 | spl5_239 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_9 | ~spl5_127),
% 3.92/0.94    inference(avatar_split_clause,[],[f2112,f1063,f108,f148,f143,f138,f2118,f118])).
% 3.92/0.94  fof(f2118,plain,(
% 3.92/0.94    spl5_239 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK2) | ~m1_pre_topc(X1,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_239])])).
% 3.92/0.94  fof(f108,plain,(
% 3.92/0.94    spl5_9 <=> m1_pre_topc(sK3,sK0)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.92/0.94  fof(f2112,plain,(
% 3.92/0.94    ( ! [X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(X1,sK2) | ~m1_pre_topc(X1,sK3)) ) | (~spl5_9 | ~spl5_127)),
% 3.92/0.94    inference(resolution,[],[f1064,f110])).
% 3.92/0.94  fof(f110,plain,(
% 3.92/0.94    m1_pre_topc(sK3,sK0) | ~spl5_9),
% 3.92/0.94    inference(avatar_component_clause,[],[f108])).
% 3.92/0.94  fof(f2107,plain,(
% 3.92/0.94    spl5_10 | spl5_238 | ~spl5_126),
% 3.92/0.94    inference(avatar_split_clause,[],[f2094,f1059,f2105,f113])).
% 3.92/0.94  fof(f2105,plain,(
% 3.92/0.94    spl5_238 <=> ! [X7,X8,X6] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X8,sK3) | r1_tsep_1(sK2,X8) | ~m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_238])])).
% 3.92/0.94  fof(f1059,plain,(
% 3.92/0.94    spl5_126 <=> ! [X5,X4] : (r1_tsep_1(sK2,X4) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(sK2,X5) | ~m1_pre_topc(sK3,X5) | ~m1_pre_topc(X4,sK3))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).
% 3.92/0.94  fof(f2094,plain,(
% 3.92/0.94    ( ! [X6,X8,X7] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(sK2,X8) | ~m1_pre_topc(X8,sK3) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_126),
% 3.92/0.94    inference(resolution,[],[f1060,f167])).
% 3.92/0.94  fof(f1060,plain,(
% 3.92/0.94    ( ! [X4,X5] : (~m1_pre_topc(sK3,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(sK2,X5) | r1_tsep_1(sK2,X4) | ~m1_pre_topc(X4,sK3)) ) | ~spl5_126),
% 3.92/0.94    inference(avatar_component_clause,[],[f1059])).
% 3.92/0.94  fof(f2103,plain,(
% 3.92/0.94    spl5_10 | spl5_237 | ~spl5_126),
% 3.92/0.94    inference(avatar_split_clause,[],[f2093,f1059,f2101,f113])).
% 3.92/0.94  fof(f2101,plain,(
% 3.92/0.94    spl5_237 <=> ! [X3,X5,X4] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X5,sK3) | r1_tsep_1(sK2,X5) | ~m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).
% 3.92/0.94  fof(f2093,plain,(
% 3.92/0.94    ( ! [X4,X5,X3] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(sK2,X5) | ~m1_pre_topc(X5,sK3) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_126),
% 3.92/0.94    inference(resolution,[],[f1060,f50])).
% 3.92/0.94  fof(f2099,plain,(
% 3.92/0.94    ~spl5_11 | spl5_236 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_9 | ~spl5_126),
% 3.92/0.94    inference(avatar_split_clause,[],[f2091,f1059,f108,f148,f143,f138,f2097,f118])).
% 3.92/0.94  fof(f2097,plain,(
% 3.92/0.94    spl5_236 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(sK2,X1) | ~m1_pre_topc(X1,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_236])])).
% 3.92/0.94  fof(f2091,plain,(
% 3.92/0.94    ( ! [X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK2,X1) | ~m1_pre_topc(X1,sK3)) ) | (~spl5_9 | ~spl5_126)),
% 3.92/0.94    inference(resolution,[],[f1060,f110])).
% 3.92/0.94  fof(f2085,plain,(
% 3.92/0.94    spl5_10 | spl5_235 | ~spl5_125),
% 3.92/0.94    inference(avatar_split_clause,[],[f2072,f1055,f2083,f113])).
% 3.92/0.94  fof(f2083,plain,(
% 3.92/0.94    spl5_235 <=> ! [X7,X8,X6] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X8,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(X8,sK3) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_235])])).
% 3.92/0.94  fof(f1055,plain,(
% 3.92/0.94    spl5_125 <=> ! [X3,X2] : (r1_tsep_1(X2,sK3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(sK2,X3) | ~m1_pre_topc(X2,sK2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).
% 3.92/0.94  fof(f2072,plain,(
% 3.92/0.94    ( ! [X6,X8,X7] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(X8,sK3) | ~m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(X8,sK2) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_125),
% 3.92/0.94    inference(resolution,[],[f1056,f167])).
% 3.92/0.94  fof(f1056,plain,(
% 3.92/0.94    ( ! [X2,X3] : (~m1_pre_topc(sK3,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X2,sK3) | ~m1_pre_topc(sK2,X3) | ~m1_pre_topc(X2,sK2)) ) | ~spl5_125),
% 3.92/0.94    inference(avatar_component_clause,[],[f1055])).
% 3.92/0.94  fof(f2081,plain,(
% 3.92/0.94    spl5_10 | spl5_234 | ~spl5_125),
% 3.92/0.94    inference(avatar_split_clause,[],[f2071,f1055,f2079,f113])).
% 3.92/0.94  fof(f2079,plain,(
% 3.92/0.94    spl5_234 <=> ! [X3,X5,X4] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(X5,sK3) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_234])])).
% 3.92/0.94  fof(f2071,plain,(
% 3.92/0.94    ( ! [X4,X5,X3] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(X5,sK3) | ~m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_125),
% 3.92/0.94    inference(resolution,[],[f1056,f50])).
% 3.92/0.94  fof(f2077,plain,(
% 3.92/0.94    ~spl5_11 | spl5_233 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_9 | ~spl5_125),
% 3.92/0.94    inference(avatar_split_clause,[],[f2069,f1055,f108,f148,f143,f138,f2075,f118])).
% 3.92/0.94  fof(f2075,plain,(
% 3.92/0.94    spl5_233 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | r1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_233])])).
% 3.92/0.94  fof(f2069,plain,(
% 3.92/0.94    ( ! [X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,sK3) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X1,sK2)) ) | (~spl5_9 | ~spl5_125)),
% 3.92/0.94    inference(resolution,[],[f1056,f110])).
% 3.92/0.94  fof(f2063,plain,(
% 3.92/0.94    spl5_10 | spl5_232 | ~spl5_124),
% 3.92/0.94    inference(avatar_split_clause,[],[f2050,f1051,f2061,f113])).
% 3.92/0.94  fof(f2061,plain,(
% 3.92/0.94    spl5_232 <=> ! [X7,X8,X6] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X8,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(sK3,X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).
% 3.92/0.94  fof(f1051,plain,(
% 3.92/0.94    spl5_124 <=> ! [X1,X0] : (r1_tsep_1(sK3,X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X0,sK2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 3.92/0.94  fof(f2050,plain,(
% 3.92/0.94    ( ! [X6,X8,X7] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(sK3,X8) | ~m1_pre_topc(sK2,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(X8,sK2) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_124),
% 3.92/0.94    inference(resolution,[],[f1052,f167])).
% 3.92/0.94  fof(f1052,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | r1_tsep_1(sK3,X0) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X0,sK2)) ) | ~spl5_124),
% 3.92/0.94    inference(avatar_component_clause,[],[f1051])).
% 3.92/0.94  fof(f2059,plain,(
% 3.92/0.94    spl5_10 | spl5_231 | ~spl5_124),
% 3.92/0.94    inference(avatar_split_clause,[],[f2049,f1051,f2057,f113])).
% 3.92/0.94  fof(f2057,plain,(
% 3.92/0.94    spl5_231 <=> ! [X3,X5,X4] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(sK3,X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_231])])).
% 3.92/0.94  fof(f2049,plain,(
% 3.92/0.94    ( ! [X4,X5,X3] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(sK3,X5) | ~m1_pre_topc(sK2,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_124),
% 3.92/0.94    inference(resolution,[],[f1052,f50])).
% 3.92/0.94  fof(f2055,plain,(
% 3.92/0.94    ~spl5_11 | spl5_230 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_9 | ~spl5_124),
% 3.92/0.94    inference(avatar_split_clause,[],[f2047,f1051,f108,f148,f143,f138,f2053,f118])).
% 3.92/0.94  fof(f2053,plain,(
% 3.92/0.94    spl5_230 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | r1_tsep_1(sK3,X1) | ~m1_pre_topc(X1,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_230])])).
% 3.92/0.94  fof(f2047,plain,(
% 3.92/0.94    ( ! [X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(sK3,X1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X1,sK2)) ) | (~spl5_9 | ~spl5_124)),
% 3.92/0.94    inference(resolution,[],[f1052,f110])).
% 3.92/0.94  fof(f2027,plain,(
% 3.92/0.94    spl5_18 | spl5_229 | ~spl5_106),
% 3.92/0.94    inference(avatar_split_clause,[],[f1986,f867,f2025,f174])).
% 3.92/0.94  fof(f2025,plain,(
% 3.92/0.94    spl5_229 <=> ! [X18,X17,X19] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | ~m1_pre_topc(k2_tsep_1(X19,X18,X17),sK0) | v2_struct_0(k2_tsep_1(X19,X18,X17)) | ~m1_pre_topc(k2_tsep_1(X19,X18,X17),sK1) | v2_struct_0(X19) | ~v2_pre_topc(X19) | ~l1_pre_topc(X19) | v2_struct_0(X18) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19) | v2_struct_0(X17) | ~m1_pre_topc(X17,X19) | r1_tsep_1(X18,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X18,X19))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_229])])).
% 3.92/0.94  fof(f1986,plain,(
% 3.92/0.94    ( ! [X19,X17,X18] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | r1_tsep_1(X18,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X17,X19) | v2_struct_0(X17) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X18,X19) | v2_struct_0(X18) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v2_struct_0(X19) | ~m1_pre_topc(k2_tsep_1(X19,X18,X17),sK1) | v2_struct_0(k2_tsep_1(X19,X18,X17)) | ~m1_pre_topc(k2_tsep_1(X19,X18,X17),sK0)) ) | ~spl5_106),
% 3.92/0.94    inference(resolution,[],[f56,f868])).
% 3.92/0.94  fof(f56,plain,(
% 3.92/0.94    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f19])).
% 3.92/0.94  fof(f2023,plain,(
% 3.92/0.94    spl5_18 | spl5_228 | ~spl5_153),
% 3.92/0.94    inference(avatar_split_clause,[],[f1985,f1445,f2021,f174])).
% 3.92/0.94  fof(f2021,plain,(
% 3.92/0.94    spl5_228 <=> ! [X16,X15,X14] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14) | ~m1_pre_topc(k2_tsep_1(X16,X15,X14),sK0) | v2_struct_0(k2_tsep_1(X16,X15,X14)) | ~m1_pre_topc(k2_tsep_1(X16,X15,X14),sK3) | v2_struct_0(X16) | ~v2_pre_topc(X16) | ~l1_pre_topc(X16) | v2_struct_0(X15) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16) | v2_struct_0(X14) | ~m1_pre_topc(X14,X16) | r1_tsep_1(X15,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X15,X16))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_228])])).
% 3.92/0.94  fof(f1985,plain,(
% 3.92/0.94    ( ! [X14,X15,X16] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14) | r1_tsep_1(X15,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X14,X16) | v2_struct_0(X14) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X15,X16) | v2_struct_0(X15) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16) | v2_struct_0(X16) | ~m1_pre_topc(k2_tsep_1(X16,X15,X14),sK3) | v2_struct_0(k2_tsep_1(X16,X15,X14)) | ~m1_pre_topc(k2_tsep_1(X16,X15,X14),sK0)) ) | ~spl5_153),
% 3.92/0.94    inference(resolution,[],[f56,f1446])).
% 3.92/0.94  fof(f2019,plain,(
% 3.92/0.94    spl5_18 | spl5_227 | ~spl5_167),
% 3.92/0.94    inference(avatar_split_clause,[],[f1984,f1574,f2017,f174])).
% 3.92/0.94  fof(f2017,plain,(
% 3.92/0.94    spl5_227 <=> ! [X11,X13,X10,X12] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(k2_tsep_1(X12,X11,X10),sK0) | ~m1_pre_topc(X13,sK1) | ~m1_pre_topc(X13,sK0) | v2_struct_0(k2_tsep_1(X12,X11,X10)) | ~m1_pre_topc(k2_tsep_1(X12,X11,X10),X13) | v2_struct_0(X13) | v2_struct_0(X12) | ~v2_pre_topc(X12) | ~l1_pre_topc(X12) | v2_struct_0(X11) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12) | v2_struct_0(X10) | ~m1_pre_topc(X10,X12) | r1_tsep_1(X11,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,X12))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_227])])).
% 3.92/0.94  fof(f1984,plain,(
% 3.92/0.94    ( ! [X12,X10,X13,X11] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | r1_tsep_1(X11,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X10,X12) | v2_struct_0(X10) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,X12) | v2_struct_0(X11) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | v2_struct_0(X13) | ~m1_pre_topc(k2_tsep_1(X12,X11,X10),X13) | v2_struct_0(k2_tsep_1(X12,X11,X10)) | ~m1_pre_topc(X13,sK0) | ~m1_pre_topc(X13,sK1) | ~m1_pre_topc(k2_tsep_1(X12,X11,X10),sK0)) ) | ~spl5_167),
% 3.92/0.94    inference(resolution,[],[f56,f1575])).
% 3.92/0.94  fof(f2015,plain,(
% 3.92/0.94    spl5_18 | spl5_226 | ~spl5_200),
% 3.92/0.94    inference(avatar_split_clause,[],[f1983,f1822,f2013,f174])).
% 3.92/0.94  fof(f2013,plain,(
% 3.92/0.94    spl5_226 <=> ! [X9,X7,X8,X6] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6) | ~m1_pre_topc(k2_tsep_1(X8,X7,X6),sK0) | ~m1_pre_topc(X9,sK3) | ~m1_pre_topc(X9,sK0) | v2_struct_0(k2_tsep_1(X8,X7,X6)) | ~m1_pre_topc(k2_tsep_1(X8,X7,X6),X9) | v2_struct_0(X9) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(X7) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X6) | ~m1_pre_topc(X6,X8) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_226])])).
% 3.92/0.94  fof(f1983,plain,(
% 3.92/0.94    ( ! [X6,X8,X7,X9] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X8) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(X8,X7,X6),X9) | v2_struct_0(k2_tsep_1(X8,X7,X6)) | ~m1_pre_topc(X9,sK0) | ~m1_pre_topc(X9,sK3) | ~m1_pre_topc(k2_tsep_1(X8,X7,X6),sK0)) ) | ~spl5_200),
% 3.92/0.94    inference(resolution,[],[f56,f1823])).
% 3.92/0.94  fof(f2011,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_10 | ~spl5_9 | spl5_8 | ~spl5_7 | spl5_1 | ~spl5_5 | ~spl5_166),
% 3.92/0.94    inference(avatar_split_clause,[],[f1982,f1555,f88,f70,f98,f103,f108,f113,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f70,plain,(
% 3.92/0.94    spl5_1 <=> r1_tsep_1(sK2,sK3)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.92/0.94  fof(f88,plain,(
% 3.92/0.94    spl5_5 <=> m1_pre_topc(sK3,sK4)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.92/0.94  fof(f1555,plain,(
% 3.92/0.94    spl5_166 <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).
% 3.92/0.94  fof(f1982,plain,(
% 3.92/0.94    ~m1_pre_topc(sK3,sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_166),
% 3.92/0.94    inference(resolution,[],[f56,f1557])).
% 3.92/0.94  fof(f1557,plain,(
% 3.92/0.94    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) | ~spl5_166),
% 3.92/0.94    inference(avatar_component_clause,[],[f1555])).
% 3.92/0.94  fof(f2010,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_225 | ~spl5_81),
% 3.92/0.94    inference(avatar_split_clause,[],[f1991,f644,f2008,f98,f103,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f2008,plain,(
% 3.92/0.94    spl5_225 <=> ! [X5] : (~m1_pre_topc(X5,sK4) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | r1_tsep_1(sK2,X5))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_225])])).
% 3.92/0.94  fof(f644,plain,(
% 3.92/0.94    spl5_81 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 3.92/0.94  fof(f1991,plain,(
% 3.92/0.94    ( ! [X5] : (~m1_pre_topc(X5,sK4) | r1_tsep_1(sK2,X5) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X5,sK1)) ) | ~spl5_81),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1979])).
% 3.92/0.94  fof(f1979,plain,(
% 3.92/0.94    ( ! [X5] : (~m1_pre_topc(X5,sK4) | r1_tsep_1(sK2,X5) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0)) ) | ~spl5_81),
% 3.92/0.94    inference(resolution,[],[f56,f645])).
% 3.92/0.94  fof(f645,plain,(
% 3.92/0.94    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_81),
% 3.92/0.94    inference(avatar_component_clause,[],[f644])).
% 3.92/0.94  fof(f2006,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_224 | ~spl5_134),
% 3.92/0.94    inference(avatar_split_clause,[],[f1992,f1193,f2004,f98,f103,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f2004,plain,(
% 3.92/0.94    spl5_224 <=> ! [X4] : (~m1_pre_topc(X4,sK4) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | r1_tsep_1(sK2,X4))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).
% 3.92/0.94  fof(f1992,plain,(
% 3.92/0.94    ( ! [X4] : (~m1_pre_topc(X4,sK4) | r1_tsep_1(sK2,X4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X4,sK3)) ) | ~spl5_134),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1978])).
% 3.92/0.94  fof(f1978,plain,(
% 3.92/0.94    ( ! [X4] : (~m1_pre_topc(X4,sK4) | r1_tsep_1(sK2,X4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0)) ) | ~spl5_134),
% 3.92/0.94    inference(resolution,[],[f56,f1194])).
% 3.92/0.94  fof(f2002,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_223 | ~spl5_188),
% 3.92/0.94    inference(avatar_split_clause,[],[f1993,f1734,f2000,f98,f103,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f2000,plain,(
% 3.92/0.94    spl5_223 <=> ! [X3,X2] : (~m1_pre_topc(X2,sK4) | ~m1_pre_topc(X3,sK1) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,X3) | v2_struct_0(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(sK2,X2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).
% 3.92/0.94  fof(f1993,plain,(
% 3.92/0.94    ( ! [X2,X3] : (~m1_pre_topc(X2,sK4) | r1_tsep_1(sK2,X2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X3,sK1)) ) | ~spl5_188),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1977])).
% 3.92/0.94  fof(f1977,plain,(
% 3.92/0.94    ( ! [X2,X3] : (~m1_pre_topc(X2,sK4) | r1_tsep_1(sK2,X2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,sK1)) ) | ~spl5_188),
% 3.92/0.94    inference(resolution,[],[f56,f1735])).
% 3.92/0.94  fof(f1998,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_222 | ~spl5_192),
% 3.92/0.94    inference(avatar_split_clause,[],[f1994,f1770,f1996,f98,f103,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f1996,plain,(
% 3.92/0.94    spl5_222 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK4) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(sK2,X0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).
% 3.92/0.94  fof(f1994,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3)) ) | ~spl5_192),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1976])).
% 3.92/0.94  fof(f1976,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_192),
% 3.92/0.94    inference(resolution,[],[f56,f1771])).
% 3.92/0.94  fof(f1957,plain,(
% 3.92/0.94    spl5_18 | spl5_221 | ~spl5_106),
% 3.92/0.94    inference(avatar_split_clause,[],[f1898,f867,f1955,f174])).
% 3.92/0.94  fof(f1955,plain,(
% 3.92/0.94    spl5_221 <=> ! [X18,X17,X19] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | ~m1_pre_topc(k2_tsep_1(X19,X18,X17),sK0) | v2_struct_0(k2_tsep_1(X19,X18,X17)) | ~m1_pre_topc(k2_tsep_1(X19,X18,X17),sK1) | v2_struct_0(X19) | ~v2_pre_topc(X19) | ~l1_pre_topc(X19) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19) | v2_struct_0(X18) | v2_struct_0(X17) | ~m1_pre_topc(X17,X19) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X18) | ~m1_pre_topc(X18,X19))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_221])])).
% 3.92/0.94  fof(f1898,plain,(
% 3.92/0.94    ( ! [X19,X17,X18] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X18) | ~m1_pre_topc(X17,X19) | v2_struct_0(X17) | ~m1_pre_topc(X18,X19) | v2_struct_0(X18) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X19) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | v2_struct_0(X19) | ~m1_pre_topc(k2_tsep_1(X19,X18,X17),sK1) | v2_struct_0(k2_tsep_1(X19,X18,X17)) | ~m1_pre_topc(k2_tsep_1(X19,X18,X17),sK0)) ) | ~spl5_106),
% 3.92/0.94    inference(resolution,[],[f55,f868])).
% 3.92/0.94  fof(f55,plain,(
% 3.92/0.94    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | ~m1_pre_topc(X1,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f19])).
% 3.92/0.94  fof(f1953,plain,(
% 3.92/0.94    spl5_18 | spl5_220 | ~spl5_153),
% 3.92/0.94    inference(avatar_split_clause,[],[f1897,f1445,f1951,f174])).
% 3.92/0.94  fof(f1951,plain,(
% 3.92/0.94    spl5_220 <=> ! [X16,X15,X14] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14) | ~m1_pre_topc(k2_tsep_1(X16,X15,X14),sK0) | v2_struct_0(k2_tsep_1(X16,X15,X14)) | ~m1_pre_topc(k2_tsep_1(X16,X15,X14),sK3) | v2_struct_0(X16) | ~v2_pre_topc(X16) | ~l1_pre_topc(X16) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16) | v2_struct_0(X15) | v2_struct_0(X14) | ~m1_pre_topc(X14,X16) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X15) | ~m1_pre_topc(X15,X16))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_220])])).
% 3.92/0.94  fof(f1897,plain,(
% 3.92/0.94    ( ! [X14,X15,X16] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X15) | ~m1_pre_topc(X14,X16) | v2_struct_0(X14) | ~m1_pre_topc(X15,X16) | v2_struct_0(X15) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16) | v2_struct_0(X16) | ~m1_pre_topc(k2_tsep_1(X16,X15,X14),sK3) | v2_struct_0(k2_tsep_1(X16,X15,X14)) | ~m1_pre_topc(k2_tsep_1(X16,X15,X14),sK0)) ) | ~spl5_153),
% 3.92/0.94    inference(resolution,[],[f55,f1446])).
% 3.92/0.94  fof(f1949,plain,(
% 3.92/0.94    spl5_18 | spl5_219 | ~spl5_167),
% 3.92/0.94    inference(avatar_split_clause,[],[f1896,f1574,f1947,f174])).
% 3.92/0.94  fof(f1947,plain,(
% 3.92/0.94    spl5_219 <=> ! [X11,X13,X10,X12] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(k2_tsep_1(X12,X11,X10),sK0) | ~m1_pre_topc(X13,sK1) | ~m1_pre_topc(X13,sK0) | v2_struct_0(k2_tsep_1(X12,X11,X10)) | ~m1_pre_topc(k2_tsep_1(X12,X11,X10),X13) | v2_struct_0(X13) | v2_struct_0(X12) | ~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12) | v2_struct_0(X11) | v2_struct_0(X10) | ~m1_pre_topc(X10,X12) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X11) | ~m1_pre_topc(X11,X12))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_219])])).
% 3.92/0.94  fof(f1896,plain,(
% 3.92/0.94    ( ! [X12,X10,X13,X11] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X11) | ~m1_pre_topc(X10,X12) | v2_struct_0(X10) | ~m1_pre_topc(X11,X12) | v2_struct_0(X11) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X12) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | v2_struct_0(X13) | ~m1_pre_topc(k2_tsep_1(X12,X11,X10),X13) | v2_struct_0(k2_tsep_1(X12,X11,X10)) | ~m1_pre_topc(X13,sK0) | ~m1_pre_topc(X13,sK1) | ~m1_pre_topc(k2_tsep_1(X12,X11,X10),sK0)) ) | ~spl5_167),
% 3.92/0.94    inference(resolution,[],[f55,f1575])).
% 3.92/0.94  fof(f1945,plain,(
% 3.92/0.94    spl5_18 | spl5_218 | ~spl5_200),
% 3.92/0.94    inference(avatar_split_clause,[],[f1895,f1822,f1943,f174])).
% 3.92/0.94  fof(f1943,plain,(
% 3.92/0.94    spl5_218 <=> ! [X9,X7,X8,X6] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6) | ~m1_pre_topc(k2_tsep_1(X8,X7,X6),sK0) | ~m1_pre_topc(X9,sK3) | ~m1_pre_topc(X9,sK0) | v2_struct_0(k2_tsep_1(X8,X7,X6)) | ~m1_pre_topc(k2_tsep_1(X8,X7,X6),X9) | v2_struct_0(X9) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X7) | v2_struct_0(X6) | ~m1_pre_topc(X6,X8) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X7,X8))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_218])])).
% 3.92/0.94  fof(f1895,plain,(
% 3.92/0.94    ( ! [X6,X8,X7,X9] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X6,X8) | v2_struct_0(X6) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(X8,X7,X6),X9) | v2_struct_0(k2_tsep_1(X8,X7,X6)) | ~m1_pre_topc(X9,sK0) | ~m1_pre_topc(X9,sK3) | ~m1_pre_topc(k2_tsep_1(X8,X7,X6),sK0)) ) | ~spl5_200),
% 3.92/0.94    inference(resolution,[],[f55,f1823])).
% 3.92/0.94  fof(f1941,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_10 | ~spl5_9 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_110 | ~spl5_5 | ~spl5_166),
% 3.92/0.94    inference(avatar_split_clause,[],[f1894,f1555,f88,f909,f98,f103,f118,f123,f108,f113,f138,f143,f148])).
% 3.92/0.94  fof(f909,plain,(
% 3.92/0.94    spl5_110 <=> r1_tsep_1(sK3,sK2)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 3.92/0.94  fof(f1894,plain,(
% 3.92/0.94    ~m1_pre_topc(sK3,sK4) | r1_tsep_1(sK3,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_166),
% 3.92/0.94    inference(resolution,[],[f55,f1557])).
% 3.92/0.94  fof(f1940,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_14 | ~spl5_13 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_216 | ~spl5_217 | ~spl5_165),
% 3.92/0.94    inference(avatar_split_clause,[],[f1893,f1550,f1937,f1933,f98,f103,f118,f123,f128,f133,f138,f143,f148])).
% 3.92/0.94  fof(f1933,plain,(
% 3.92/0.94    spl5_216 <=> r1_tsep_1(sK1,sK2)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_216])])).
% 3.92/0.94  fof(f1937,plain,(
% 3.92/0.94    spl5_217 <=> m1_pre_topc(sK1,sK4)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_217])])).
% 3.92/0.94  fof(f1893,plain,(
% 3.92/0.94    ~m1_pre_topc(sK1,sK4) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_165),
% 3.92/0.94    inference(resolution,[],[f55,f1552])).
% 3.92/0.94  fof(f1931,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_19 | ~spl5_22 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_214 | ~spl5_215 | ~spl5_4),
% 3.92/0.94    inference(avatar_split_clause,[],[f1892,f83,f1928,f1924,f98,f103,f118,f123,f200,f178,f138,f143,f148])).
% 3.92/0.94  fof(f178,plain,(
% 3.92/0.94    spl5_19 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 3.92/0.94  fof(f200,plain,(
% 3.92/0.94    spl5_22 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 3.92/0.94  fof(f1924,plain,(
% 3.92/0.94    spl5_214 <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).
% 3.92/0.94  fof(f1928,plain,(
% 3.92/0.94    spl5_215 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).
% 3.92/0.94  fof(f83,plain,(
% 3.92/0.94    spl5_4 <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.92/0.94  fof(f1892,plain,(
% 3.92/0.94    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 3.92/0.94    inference(resolution,[],[f55,f85])).
% 3.92/0.94  fof(f85,plain,(
% 3.92/0.94    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | ~spl5_4),
% 3.92/0.94    inference(avatar_component_clause,[],[f83])).
% 3.92/0.94  fof(f1922,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_213 | ~spl5_81),
% 3.92/0.94    inference(avatar_split_clause,[],[f1903,f644,f1920,f98,f103,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f1920,plain,(
% 3.92/0.94    spl5_213 <=> ! [X5] : (~m1_pre_topc(X5,sK4) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | r1_tsep_1(X5,sK2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).
% 3.92/0.94  fof(f1903,plain,(
% 3.92/0.94    ( ! [X5] : (~m1_pre_topc(X5,sK4) | r1_tsep_1(X5,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X5,sK1)) ) | ~spl5_81),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1891])).
% 3.92/0.94  fof(f1891,plain,(
% 3.92/0.94    ( ! [X5] : (~m1_pre_topc(X5,sK4) | r1_tsep_1(X5,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0)) ) | ~spl5_81),
% 3.92/0.94    inference(resolution,[],[f55,f645])).
% 3.92/0.94  fof(f1918,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_212 | ~spl5_134),
% 3.92/0.94    inference(avatar_split_clause,[],[f1904,f1193,f1916,f98,f103,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f1916,plain,(
% 3.92/0.94    spl5_212 <=> ! [X4] : (~m1_pre_topc(X4,sK4) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | r1_tsep_1(X4,sK2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_212])])).
% 3.92/0.94  fof(f1904,plain,(
% 3.92/0.94    ( ! [X4] : (~m1_pre_topc(X4,sK4) | r1_tsep_1(X4,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X4,sK3)) ) | ~spl5_134),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1890])).
% 3.92/0.94  fof(f1890,plain,(
% 3.92/0.94    ( ! [X4] : (~m1_pre_topc(X4,sK4) | r1_tsep_1(X4,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0)) ) | ~spl5_134),
% 3.92/0.94    inference(resolution,[],[f55,f1194])).
% 3.92/0.94  fof(f1914,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_211 | ~spl5_188),
% 3.92/0.94    inference(avatar_split_clause,[],[f1905,f1734,f1912,f98,f103,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f1912,plain,(
% 3.92/0.94    spl5_211 <=> ! [X3,X2] : (~m1_pre_topc(X2,sK4) | ~m1_pre_topc(X3,sK1) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,X3) | v2_struct_0(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(X2,sK2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_211])])).
% 3.92/0.94  fof(f1905,plain,(
% 3.92/0.94    ( ! [X2,X3] : (~m1_pre_topc(X2,sK4) | r1_tsep_1(X2,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X3,sK1)) ) | ~spl5_188),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1889])).
% 3.92/0.94  fof(f1889,plain,(
% 3.92/0.94    ( ! [X2,X3] : (~m1_pre_topc(X2,sK4) | r1_tsep_1(X2,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,sK1)) ) | ~spl5_188),
% 3.92/0.94    inference(resolution,[],[f55,f1735])).
% 3.92/0.94  fof(f1910,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_210 | ~spl5_192),
% 3.92/0.94    inference(avatar_split_clause,[],[f1906,f1770,f1908,f98,f103,f118,f123,f138,f143,f148])).
% 3.92/0.94  fof(f1908,plain,(
% 3.92/0.94    spl5_210 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK4) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,sK2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).
% 3.92/0.94  fof(f1906,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3)) ) | ~spl5_192),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1888])).
% 3.92/0.94  fof(f1888,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_192),
% 3.92/0.94    inference(resolution,[],[f55,f1771])).
% 3.92/0.94  fof(f1884,plain,(
% 3.92/0.94    spl5_18 | spl5_209 | ~spl5_146),
% 3.92/0.94    inference(avatar_split_clause,[],[f1870,f1335,f1882,f174])).
% 3.92/0.94  fof(f1882,plain,(
% 3.92/0.94    spl5_209 <=> ! [X9,X11,X8,X10] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X9) | ~m1_pre_topc(X9,X8) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | r1_tsep_1(X10,X11) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK3) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).
% 3.92/0.94  fof(f1335,plain,(
% 3.92/0.94    spl5_146 <=> ! [X9,X11,X10] : (~m1_pre_topc(X9,sK3) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(X10) | ~m1_pre_topc(X10,X11) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | ~m1_pre_topc(X9,X11) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X10,X9) | ~m1_pre_topc(X9,sK0) | v2_struct_0(X9))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).
% 3.92/0.94  fof(f1870,plain,(
% 3.92/0.94    ( ! [X10,X8,X11,X9] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK3) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X10,X11) | ~m1_pre_topc(X11,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_146),
% 3.92/0.94    inference(resolution,[],[f1336,f167])).
% 3.92/0.94  fof(f1336,plain,(
% 3.92/0.94    ( ! [X10,X11,X9] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(X10) | ~m1_pre_topc(X10,X11) | ~m1_pre_topc(X9,sK3) | ~m1_pre_topc(X9,X11) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X10,X9) | ~m1_pre_topc(X9,sK0) | v2_struct_0(X9)) ) | ~spl5_146),
% 3.92/0.94    inference(avatar_component_clause,[],[f1335])).
% 3.92/0.94  fof(f1880,plain,(
% 3.92/0.94    spl5_18 | spl5_208 | ~spl5_146),
% 3.92/0.94    inference(avatar_split_clause,[],[f1869,f1335,f1878,f174])).
% 3.92/0.94  fof(f1878,plain,(
% 3.92/0.94    spl5_208 <=> ! [X5,X7,X4,X6] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | r1_tsep_1(X6,X7) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).
% 3.92/0.94  fof(f1869,plain,(
% 3.92/0.94    ( ! [X6,X4,X7,X5] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X6,X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_146),
% 3.92/0.94    inference(resolution,[],[f1336,f50])).
% 3.92/0.94  fof(f1876,plain,(
% 3.92/0.94    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_207 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_146),
% 3.92/0.94    inference(avatar_split_clause,[],[f1872,f1335,f148,f143,f138,f1874,f98,f103,f118,f123])).
% 3.92/0.94  fof(f1874,plain,(
% 3.92/0.94    spl5_207 <=> ! [X1,X0] : (v2_struct_0(X0) | v2_struct_0(X1) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).
% 3.92/0.94  fof(f1872,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X0,X1) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_146),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1867])).
% 3.92/0.94  fof(f1867,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_146),
% 3.92/0.94    inference(resolution,[],[f1336,f68])).
% 3.92/0.94  fof(f68,plain,(
% 3.92/0.94    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f27])).
% 3.92/0.94  fof(f27,plain,(
% 3.92/0.94    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.92/0.94    inference(flattening,[],[f26])).
% 3.92/0.94  fof(f26,plain,(
% 3.92/0.94    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.92/0.94    inference(ennf_transformation,[],[f3])).
% 3.92/0.94  fof(f3,axiom,(
% 3.92/0.94    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.92/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 3.92/0.94  fof(f1863,plain,(
% 3.92/0.94    spl5_18 | spl5_206 | ~spl5_145),
% 3.92/0.94    inference(avatar_split_clause,[],[f1849,f1331,f1861,f174])).
% 3.92/0.94  fof(f1861,plain,(
% 3.92/0.94    spl5_206 <=> ! [X9,X11,X8,X10] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X9) | ~m1_pre_topc(X9,X8) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | r1_tsep_1(X11,X10) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK3) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).
% 3.92/0.94  fof(f1331,plain,(
% 3.92/0.94    spl5_145 <=> ! [X7,X8,X6] : (~m1_pre_topc(X6,sK3) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(X7) | ~m1_pre_topc(X7,X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | ~m1_pre_topc(X6,X8) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X6,X7) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).
% 3.92/0.94  fof(f1849,plain,(
% 3.92/0.94    ( ! [X10,X8,X11,X9] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK3) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X11,X10) | ~m1_pre_topc(X11,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_145),
% 3.92/0.94    inference(resolution,[],[f1332,f167])).
% 3.92/0.94  fof(f1332,plain,(
% 3.92/0.94    ( ! [X6,X8,X7] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(X7) | ~m1_pre_topc(X7,X8) | ~m1_pre_topc(X6,sK3) | ~m1_pre_topc(X6,X8) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X6,X7) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6)) ) | ~spl5_145),
% 3.92/0.94    inference(avatar_component_clause,[],[f1331])).
% 3.92/0.94  fof(f1859,plain,(
% 3.92/0.94    spl5_18 | spl5_205 | ~spl5_145),
% 3.92/0.94    inference(avatar_split_clause,[],[f1848,f1331,f1857,f174])).
% 3.92/0.94  fof(f1857,plain,(
% 3.92/0.94    spl5_205 <=> ! [X5,X7,X4,X6] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | r1_tsep_1(X7,X6) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).
% 3.92/0.94  fof(f1848,plain,(
% 3.92/0.94    ( ! [X6,X4,X7,X5] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_145),
% 3.92/0.94    inference(resolution,[],[f1332,f50])).
% 3.92/0.94  fof(f1855,plain,(
% 3.92/0.94    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_204 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_145),
% 3.92/0.94    inference(avatar_split_clause,[],[f1851,f1331,f148,f143,f138,f1853,f98,f103,f118,f123])).
% 3.92/0.94  fof(f1853,plain,(
% 3.92/0.94    spl5_204 <=> ! [X1,X0] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).
% 3.92/0.94  fof(f1851,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_145),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1846])).
% 3.92/0.94  fof(f1846,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_145),
% 3.92/0.94    inference(resolution,[],[f1332,f68])).
% 3.92/0.94  fof(f1845,plain,(
% 3.92/0.94    spl5_18 | spl5_203 | ~spl5_200),
% 3.92/0.94    inference(avatar_split_clause,[],[f1837,f1822,f1843,f174])).
% 3.92/0.94  fof(f1843,plain,(
% 3.92/0.94    spl5_203 <=> ! [X16,X18,X17,X19] : (v2_struct_0(X16) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | v2_struct_0(X19) | ~m1_pre_topc(X19,X17) | v2_struct_0(X18) | ~m1_pre_topc(X18,X17) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X19) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X18) | ~m1_pre_topc(k2_tsep_1(X17,X18,X19),sK0) | ~m1_pre_topc(X16,sK3) | ~m1_pre_topc(X16,sK0) | v2_struct_0(k2_tsep_1(X17,X18,X19)) | ~m1_pre_topc(k2_tsep_1(X17,X18,X19),X16))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).
% 3.92/0.94  fof(f1837,plain,(
% 3.92/0.94    ( ! [X19,X17,X18,X16] : (v2_struct_0(X16) | ~m1_pre_topc(k2_tsep_1(X17,X18,X19),X16) | v2_struct_0(k2_tsep_1(X17,X18,X19)) | ~m1_pre_topc(X16,sK0) | ~m1_pre_topc(X16,sK3) | ~m1_pre_topc(k2_tsep_1(X17,X18,X19),sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X18) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X19) | ~m1_pre_topc(X18,X17) | v2_struct_0(X18) | ~m1_pre_topc(X19,X17) | v2_struct_0(X19) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | v2_struct_0(X17)) ) | ~spl5_200),
% 3.92/0.94    inference(resolution,[],[f1823,f54])).
% 3.92/0.94  fof(f54,plain,(
% 3.92/0.94    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) | ~m1_pre_topc(X1,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f19])).
% 3.92/0.94  fof(f1832,plain,(
% 3.92/0.94    spl5_18 | spl5_202 | ~spl5_144),
% 3.92/0.94    inference(avatar_split_clause,[],[f1818,f1327,f1830,f174])).
% 3.92/0.94  fof(f1830,plain,(
% 3.92/0.94    spl5_202 <=> ! [X9,X11,X8,X10] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X9) | ~m1_pre_topc(X9,X8) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | ~m1_pre_topc(X10,X11) | r1_tsep_1(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,sK3) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).
% 3.92/0.94  fof(f1327,plain,(
% 3.92/0.94    spl5_144 <=> ! [X3,X5,X4] : (~m1_pre_topc(X3,sK3) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).
% 3.92/0.94  fof(f1818,plain,(
% 3.92/0.94    ( ! [X10,X8,X11,X9] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK3) | r1_tsep_1(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X10,X11) | ~m1_pre_topc(X11,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_144),
% 3.92/0.94    inference(resolution,[],[f1328,f167])).
% 3.92/0.94  fof(f1328,plain,(
% 3.92/0.94    ( ! [X4,X5,X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X3,sK3) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3)) ) | ~spl5_144),
% 3.92/0.94    inference(avatar_component_clause,[],[f1327])).
% 3.92/0.94  fof(f1828,plain,(
% 3.92/0.94    spl5_18 | spl5_201 | ~spl5_144),
% 3.92/0.94    inference(avatar_split_clause,[],[f1817,f1327,f1826,f174])).
% 3.92/0.94  fof(f1826,plain,(
% 3.92/0.94    spl5_201 <=> ! [X5,X7,X4,X6] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~m1_pre_topc(X6,X7) | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).
% 3.92/0.94  fof(f1817,plain,(
% 3.92/0.94    ( ! [X6,X4,X7,X5] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK3) | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_144),
% 3.92/0.94    inference(resolution,[],[f1328,f50])).
% 3.92/0.94  fof(f1824,plain,(
% 3.92/0.94    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_200 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_144),
% 3.92/0.94    inference(avatar_split_clause,[],[f1820,f1327,f148,f143,f138,f1822,f98,f103,f118,f123])).
% 3.92/0.94  fof(f1820,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_144),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1815])).
% 3.92/0.94  fof(f1815,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_144),
% 3.92/0.94    inference(resolution,[],[f1328,f68])).
% 3.92/0.94  fof(f1810,plain,(
% 3.92/0.94    spl5_18 | spl5_199 | ~spl5_192),
% 3.92/0.94    inference(avatar_split_clause,[],[f1786,f1770,f1808,f174])).
% 3.92/0.94  fof(f1808,plain,(
% 3.92/0.94    spl5_199 <=> ! [X16,X15,X17,X14] : (v2_struct_0(X14) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | v2_struct_0(X16) | ~m1_pre_topc(X16,X17) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | ~m1_pre_topc(X15,X17) | ~m1_pre_topc(X16,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X16,X15) | ~m1_pre_topc(X15,sK0) | ~m1_pre_topc(X14,sK3) | ~m1_pre_topc(X14,sK0) | v2_struct_0(X15) | ~m1_pre_topc(X15,X14))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).
% 3.92/0.94  fof(f1786,plain,(
% 3.92/0.94    ( ! [X14,X17,X15,X16] : (v2_struct_0(X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X15) | ~m1_pre_topc(X14,sK0) | ~m1_pre_topc(X14,sK3) | ~m1_pre_topc(X15,sK0) | r1_tsep_1(X16,X15) | ~m1_pre_topc(X16,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X15,X17) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X16,X17) | v2_struct_0(X16) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | v2_struct_0(X17)) ) | ~spl5_192),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1785])).
% 3.92/0.94  fof(f1785,plain,(
% 3.92/0.94    ( ! [X14,X17,X15,X16] : (v2_struct_0(X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X15) | ~m1_pre_topc(X14,sK0) | ~m1_pre_topc(X14,sK3) | ~m1_pre_topc(X15,sK0) | r1_tsep_1(X16,X15) | ~m1_pre_topc(X16,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X15,X17) | v2_struct_0(X15) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X17) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X16,X17) | v2_struct_0(X16) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | v2_struct_0(X17)) ) | ~spl5_192),
% 3.92/0.94    inference(resolution,[],[f1771,f58])).
% 3.92/0.94  fof(f58,plain,(
% 3.92/0.94    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f21])).
% 3.92/0.94  fof(f21,plain,(
% 3.92/0.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.92/0.94    inference(flattening,[],[f20])).
% 3.92/0.94  fof(f20,plain,(
% 3.92/0.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.92/0.94    inference(ennf_transformation,[],[f5])).
% 3.92/0.94  fof(f5,axiom,(
% 3.92/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.92/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 3.92/0.94  fof(f1806,plain,(
% 3.92/0.94    spl5_18 | spl5_198 | ~spl5_192),
% 3.92/0.94    inference(avatar_split_clause,[],[f1787,f1770,f1804,f174])).
% 3.92/0.94  fof(f1804,plain,(
% 3.92/0.94    spl5_198 <=> ! [X11,X13,X10,X12] : (v2_struct_0(X10) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | v2_struct_0(X12) | ~m1_pre_topc(X12,X13) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X13) | ~m1_pre_topc(X11,X13) | ~m1_pre_topc(X12,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X11,X12) | ~m1_pre_topc(X11,sK0) | ~m1_pre_topc(X10,sK3) | ~m1_pre_topc(X10,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X11,X10))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).
% 3.92/0.94  fof(f1787,plain,(
% 3.92/0.94    ( ! [X12,X10,X13,X11] : (v2_struct_0(X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X11) | ~m1_pre_topc(X10,sK0) | ~m1_pre_topc(X10,sK3) | ~m1_pre_topc(X11,sK0) | r1_tsep_1(X11,X12) | ~m1_pre_topc(X12,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,X13) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X13) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X12,X13) | v2_struct_0(X12) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | v2_struct_0(X13)) ) | ~spl5_192),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1784])).
% 3.92/0.94  fof(f1784,plain,(
% 3.92/0.94    ( ! [X12,X10,X13,X11] : (v2_struct_0(X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X11) | ~m1_pre_topc(X10,sK0) | ~m1_pre_topc(X10,sK3) | ~m1_pre_topc(X11,sK0) | r1_tsep_1(X11,X12) | ~m1_pre_topc(X12,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,X13) | v2_struct_0(X11) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X13) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X12,X13) | v2_struct_0(X12) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | v2_struct_0(X13)) ) | ~spl5_192),
% 3.92/0.94    inference(resolution,[],[f1771,f59])).
% 3.92/0.94  fof(f59,plain,(
% 3.92/0.94    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X2,X3) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f21])).
% 3.92/0.94  fof(f1802,plain,(
% 3.92/0.94    spl5_18 | spl5_197 | ~spl5_192),
% 3.92/0.94    inference(avatar_split_clause,[],[f1788,f1770,f1800,f174])).
% 3.92/0.94  fof(f1800,plain,(
% 3.92/0.94    spl5_197 <=> ! [X9,X7,X8,X6] : (v2_struct_0(X6) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(X8) | ~m1_pre_topc(X8,X9) | ~m1_pre_topc(X7,X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9) | r1_tsep_1(X8,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X8,X7) | ~m1_pre_topc(X7,sK0) | ~m1_pre_topc(X6,sK3) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).
% 3.92/0.94  fof(f1788,plain,(
% 3.92/0.94    ( ! [X6,X8,X7,X9] : (v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(X6,sK0) | ~m1_pre_topc(X6,sK3) | ~m1_pre_topc(X7,sK0) | r1_tsep_1(X8,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X8,X7) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X9) | ~m1_pre_topc(X8,X9) | v2_struct_0(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) ) | ~spl5_192),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1783])).
% 3.92/0.94  fof(f1783,plain,(
% 3.92/0.94    ( ! [X6,X8,X7,X9] : (v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(X6,sK0) | ~m1_pre_topc(X6,sK3) | ~m1_pre_topc(X7,sK0) | r1_tsep_1(X8,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X8,X7) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X9) | v2_struct_0(X7) | ~m1_pre_topc(X8,X9) | v2_struct_0(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) ) | ~spl5_192),
% 3.92/0.94    inference(resolution,[],[f1771,f60])).
% 3.92/0.94  fof(f60,plain,(
% 3.92/0.94    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,X2) | r1_tsep_1(X1,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f21])).
% 3.92/0.94  fof(f1798,plain,(
% 3.92/0.94    spl5_18 | spl5_196 | ~spl5_192),
% 3.92/0.94    inference(avatar_split_clause,[],[f1789,f1770,f1796,f174])).
% 3.92/0.94  fof(f1796,plain,(
% 3.92/0.94    spl5_196 <=> ! [X3,X5,X2,X4] : (v2_struct_0(X2) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).
% 3.92/0.94  fof(f1789,plain,(
% 3.92/0.94    ( ! [X4,X2,X5,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X3,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_192),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1782])).
% 3.92/0.94  fof(f1782,plain,(
% 3.92/0.94    ( ! [X4,X2,X5,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X3,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_192),
% 3.92/0.94    inference(resolution,[],[f1771,f61])).
% 3.92/0.94  fof(f61,plain,(
% 3.92/0.94    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.92/0.94    inference(cnf_transformation,[],[f21])).
% 3.92/0.94  fof(f1794,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_195 | ~spl5_192),
% 3.92/0.94    inference(avatar_split_clause,[],[f1790,f1770,f1792,f118,f123,f98,f103,f138,f143,f148])).
% 3.92/0.94  fof(f1792,plain,(
% 3.92/0.94    spl5_195 <=> ! [X1,X0] : (v2_struct_0(X0) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_195])])).
% 3.92/0.94  fof(f1790,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK2) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_192),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1781])).
% 3.92/0.94  fof(f1781,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK2) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_192),
% 3.92/0.94    inference(resolution,[],[f1771,f54])).
% 3.92/0.94  fof(f1780,plain,(
% 3.92/0.94    spl5_18 | spl5_194 | ~spl5_143),
% 3.92/0.94    inference(avatar_split_clause,[],[f1766,f1323,f1778,f174])).
% 3.92/0.94  fof(f1778,plain,(
% 3.92/0.94    spl5_194 <=> ! [X9,X11,X8,X10] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X9) | ~m1_pre_topc(X9,X8) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | ~m1_pre_topc(X10,X11) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(X11,sK3) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).
% 3.92/0.94  fof(f1323,plain,(
% 3.92/0.94    spl5_143 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).
% 3.92/0.94  fof(f1766,plain,(
% 3.92/0.94    ( ! [X10,X8,X11,X9] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(X10,X11) | ~m1_pre_topc(X11,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_143),
% 3.92/0.94    inference(resolution,[],[f1324,f167])).
% 3.92/0.94  fof(f1324,plain,(
% 3.92/0.94    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X0,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl5_143),
% 3.92/0.94    inference(avatar_component_clause,[],[f1323])).
% 3.92/0.94  fof(f1776,plain,(
% 3.92/0.94    spl5_18 | spl5_193 | ~spl5_143),
% 3.92/0.94    inference(avatar_split_clause,[],[f1765,f1323,f1774,f174])).
% 3.92/0.94  fof(f1774,plain,(
% 3.92/0.94    spl5_193 <=> ! [X5,X7,X4,X6] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~m1_pre_topc(X6,X7) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).
% 3.92/0.94  fof(f1765,plain,(
% 3.92/0.94    ( ! [X6,X4,X7,X5] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_143),
% 3.92/0.94    inference(resolution,[],[f1324,f50])).
% 3.92/0.94  fof(f1772,plain,(
% 3.92/0.94    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_192 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_143),
% 3.92/0.94    inference(avatar_split_clause,[],[f1768,f1323,f148,f143,f138,f1770,f98,f103,f118,f123])).
% 3.92/0.94  fof(f1768,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_143),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1763])).
% 3.92/0.94  fof(f1763,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_143),
% 3.92/0.94    inference(resolution,[],[f1324,f68])).
% 3.92/0.94  fof(f1758,plain,(
% 3.92/0.94    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_191 | ~spl5_188),
% 3.92/0.94    inference(avatar_split_clause,[],[f1754,f1734,f1756,f118,f123,f98,f103,f138,f143,f148])).
% 3.92/0.94  fof(f1756,plain,(
% 3.92/0.94    spl5_191 <=> ! [X1,X0] : (v2_struct_0(X0) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).
% 3.92/0.94  fof(f1754,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X1,sK2) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_188),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1745])).
% 3.92/0.94  fof(f1745,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X1,sK2) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_188),
% 3.92/0.94    inference(resolution,[],[f1735,f54])).
% 3.92/0.94  fof(f1744,plain,(
% 3.92/0.94    spl5_18 | spl5_190 | ~spl5_115),
% 3.92/0.94    inference(avatar_split_clause,[],[f1730,f959,f1742,f174])).
% 3.92/0.94  fof(f1742,plain,(
% 3.92/0.94    spl5_190 <=> ! [X9,X11,X8,X10] : (~m1_pre_topc(X8,sK0) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9) | v2_struct_0(X10) | ~m1_pre_topc(X10,X9) | ~m1_pre_topc(X11,X8) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X11) | ~m1_pre_topc(X8,k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | v2_struct_0(X11) | v2_struct_0(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X8,sK1))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).
% 3.92/0.94  fof(f959,plain,(
% 3.92/0.94    spl5_115 <=> ! [X1,X0,X2] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | ~m1_pre_topc(X0,X1))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).
% 3.92/0.94  fof(f1730,plain,(
% 3.92/0.94    ( ! [X10,X8,X11,X9] : (~m1_pre_topc(X8,sK0) | ~m1_pre_topc(X8,sK1) | v2_struct_0(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X11) | ~m1_pre_topc(X11,k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X9,X10,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X11) | ~m1_pre_topc(X11,X8) | ~m1_pre_topc(X10,X9) | v2_struct_0(X10) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) ) | ~spl5_115),
% 3.92/0.94    inference(resolution,[],[f960,f167])).
% 3.92/0.94  fof(f960,plain,(
% 3.92/0.94    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,X1)) ) | ~spl5_115),
% 3.92/0.94    inference(avatar_component_clause,[],[f959])).
% 3.92/0.94  fof(f1740,plain,(
% 3.92/0.94    spl5_18 | spl5_189 | ~spl5_115),
% 3.92/0.94    inference(avatar_split_clause,[],[f1729,f959,f1738,f174])).
% 3.92/0.94  fof(f1738,plain,(
% 3.92/0.94    spl5_189 <=> ! [X5,X7,X4,X6] : (~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,X4) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X4,k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | v2_struct_0(X4) | v2_struct_0(X7) | v2_struct_0(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | ~m1_pre_topc(X7,k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | ~l1_pre_topc(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | ~v2_pre_topc(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | ~m1_pre_topc(X4,sK1))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_189])])).
% 3.92/0.94  fof(f1729,plain,(
% 3.92/0.94    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X4,sK1) | v2_struct_0(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | ~v2_pre_topc(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | ~l1_pre_topc(k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X5,k2_tsep_1(sK0,sK2,sK4),X6)) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X7,X4) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_115),
% 3.92/0.94    inference(resolution,[],[f960,f50])).
% 3.92/0.94  fof(f1736,plain,(
% 3.92/0.94    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_15 | ~spl5_16 | spl5_17 | spl5_188 | ~spl5_115),
% 3.92/0.94    inference(avatar_split_clause,[],[f1732,f959,f1734,f148,f143,f138,f98,f103,f118,f123])).
% 3.92/0.94  fof(f1732,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_115),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1727])).
% 3.92/0.94  fof(f1727,plain,(
% 3.92/0.94    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_115),
% 3.92/0.94    inference(resolution,[],[f960,f68])).
% 3.92/0.94  fof(f1723,plain,(
% 3.92/0.94    spl5_18 | spl5_187 | ~spl5_89),
% 3.92/0.94    inference(avatar_split_clause,[],[f1709,f702,f1721,f174])).
% 3.92/0.94  fof(f1721,plain,(
% 3.92/0.94    spl5_187 <=> ! [X9,X11,X8,X10] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X9) | ~m1_pre_topc(X9,X8) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | r1_tsep_1(X10,X11) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK1) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).
% 3.92/0.94  fof(f702,plain,(
% 3.92/0.94    spl5_89 <=> ! [X7,X8,X6] : (~m1_pre_topc(X6,sK1) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(X7) | ~m1_pre_topc(X7,X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | ~m1_pre_topc(X6,X8) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X7,X6) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 3.92/0.94  fof(f1709,plain,(
% 3.92/0.94    ( ! [X10,X8,X11,X9] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK1) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X10,X11) | ~m1_pre_topc(X11,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_89),
% 3.92/0.94    inference(resolution,[],[f703,f167])).
% 3.92/0.94  fof(f703,plain,(
% 3.92/0.94    ( ! [X6,X8,X7] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(X7) | ~m1_pre_topc(X7,X8) | ~m1_pre_topc(X6,sK1) | ~m1_pre_topc(X6,X8) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X7,X6) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6)) ) | ~spl5_89),
% 3.92/0.94    inference(avatar_component_clause,[],[f702])).
% 3.92/0.94  fof(f1719,plain,(
% 3.92/0.94    spl5_18 | spl5_186 | ~spl5_89),
% 3.92/0.94    inference(avatar_split_clause,[],[f1708,f702,f1717,f174])).
% 3.92/0.94  fof(f1717,plain,(
% 3.92/0.94    spl5_186 <=> ! [X5,X7,X4,X6] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | r1_tsep_1(X6,X7) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).
% 3.92/0.94  fof(f1708,plain,(
% 3.92/0.94    ( ! [X6,X4,X7,X5] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X6,X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_89),
% 3.92/0.94    inference(resolution,[],[f703,f50])).
% 3.92/0.94  fof(f1715,plain,(
% 3.92/0.94    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_185 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_89),
% 3.92/0.94    inference(avatar_split_clause,[],[f1711,f702,f148,f143,f138,f1713,f98,f103,f118,f123])).
% 3.92/0.94  fof(f1713,plain,(
% 3.92/0.94    spl5_185 <=> ! [X1,X0] : (v2_struct_0(X0) | v2_struct_0(X1) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).
% 3.92/0.94  fof(f1711,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X0,X1) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_89),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1706])).
% 3.92/0.94  fof(f1706,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_89),
% 3.92/0.94    inference(resolution,[],[f703,f68])).
% 3.92/0.94  fof(f1702,plain,(
% 3.92/0.94    spl5_18 | spl5_184 | ~spl5_88),
% 3.92/0.94    inference(avatar_split_clause,[],[f1688,f698,f1700,f174])).
% 3.92/0.94  fof(f1700,plain,(
% 3.92/0.94    spl5_184 <=> ! [X9,X11,X8,X10] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X9) | ~m1_pre_topc(X9,X8) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | r1_tsep_1(X11,X10) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK1) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).
% 3.92/0.94  fof(f698,plain,(
% 3.92/0.94    spl5_88 <=> ! [X3,X5,X4] : (~m1_pre_topc(X3,sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X3,X4) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 3.92/0.94  fof(f1688,plain,(
% 3.92/0.94    ( ! [X10,X8,X11,X9] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK1) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X11,X10) | ~m1_pre_topc(X11,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_88),
% 3.92/0.94    inference(resolution,[],[f699,f167])).
% 3.92/0.94  fof(f699,plain,(
% 3.92/0.94    ( ! [X4,X5,X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X3,sK1) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X3,X4) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3)) ) | ~spl5_88),
% 3.92/0.94    inference(avatar_component_clause,[],[f698])).
% 3.92/0.94  fof(f1698,plain,(
% 3.92/0.94    spl5_18 | spl5_183 | ~spl5_88),
% 3.92/0.94    inference(avatar_split_clause,[],[f1687,f698,f1696,f174])).
% 3.92/0.94  fof(f1696,plain,(
% 3.92/0.94    spl5_183 <=> ! [X5,X7,X4,X6] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | r1_tsep_1(X7,X6) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).
% 3.92/0.94  fof(f1687,plain,(
% 3.92/0.94    ( ! [X6,X4,X7,X5] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_88),
% 3.92/0.94    inference(resolution,[],[f699,f50])).
% 3.92/0.94  fof(f1694,plain,(
% 3.92/0.94    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_182 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_88),
% 3.92/0.94    inference(avatar_split_clause,[],[f1690,f698,f148,f143,f138,f1692,f98,f103,f118,f123])).
% 3.92/0.94  fof(f1692,plain,(
% 3.92/0.94    spl5_182 <=> ! [X1,X0] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,sK1) | r1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).
% 3.92/0.94  fof(f1690,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_88),
% 3.92/0.94    inference(duplicate_literal_removal,[],[f1685])).
% 3.92/0.94  fof(f1685,plain,(
% 3.92/0.94    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_88),
% 3.92/0.94    inference(resolution,[],[f699,f68])).
% 3.92/0.94  fof(f1657,plain,(
% 3.92/0.94    spl5_18 | spl5_181 | ~spl5_106),
% 3.92/0.94    inference(avatar_split_clause,[],[f1616,f867,f1655,f174])).
% 3.92/0.94  fof(f1655,plain,(
% 3.92/0.94    spl5_181 <=> ! [X9,X11,X10] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9) | ~m1_pre_topc(k2_tsep_1(X11,X9,X10),sK0) | v2_struct_0(k2_tsep_1(X11,X9,X10)) | ~m1_pre_topc(k2_tsep_1(X11,X9,X10),sK1) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | v2_struct_0(X10) | v2_struct_0(X9) | ~m1_pre_topc(X9,X11) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(X10,X11))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).
% 3.92/0.94  fof(f1616,plain,(
% 3.92/0.94    ( ! [X10,X11,X9] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X9) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(X9,X11) | v2_struct_0(X9) | ~m1_pre_topc(X10,X11) | v2_struct_0(X10) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11) | ~m1_pre_topc(k2_tsep_1(X11,X9,X10),sK1) | v2_struct_0(k2_tsep_1(X11,X9,X10)) | ~m1_pre_topc(k2_tsep_1(X11,X9,X10),sK0)) ) | ~spl5_106),
% 3.92/0.94    inference(resolution,[],[f54,f868])).
% 3.92/0.94  fof(f1653,plain,(
% 3.92/0.94    spl5_18 | spl5_180 | ~spl5_153),
% 3.92/0.94    inference(avatar_split_clause,[],[f1615,f1445,f1651,f174])).
% 3.92/0.94  fof(f1651,plain,(
% 3.92/0.94    spl5_180 <=> ! [X7,X8,X6] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6) | ~m1_pre_topc(k2_tsep_1(X8,X6,X7),sK0) | v2_struct_0(k2_tsep_1(X8,X6,X7)) | ~m1_pre_topc(k2_tsep_1(X8,X6,X7),sK3) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X7) | v2_struct_0(X6) | ~m1_pre_topc(X6,X8) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X7,X8))),
% 3.92/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).
% 3.92/0.94  fof(f1615,plain,(
% 3.92/0.94    ( ! [X6,X8,X7] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X6,X8) | v2_struct_0(X6) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(k2_tsep_1(X8,X6,X7),sK3) | v2_struct_0(k2_tsep_1(X8,X6,X7)) | ~m1_pre_topc(k2_tsep_1(X8,X6,X7),sK0)) ) | ~spl5_153),
% 3.92/0.94    inference(resolution,[],[f54,f1446])).
% 3.92/0.94  fof(f1649,plain,(
% 3.92/0.94    spl5_18 | spl5_179 | ~spl5_167),
% 3.92/0.94    inference(avatar_split_clause,[],[f1614,f1574,f1647,f174])).
% 3.92/0.95  fof(f1647,plain,(
% 3.92/0.95    spl5_179 <=> ! [X3,X5,X2,X4] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | ~m1_pre_topc(k2_tsep_1(X4,X2,X3),sK0) | ~m1_pre_topc(X5,sK1) | ~m1_pre_topc(X5,sK0) | v2_struct_0(k2_tsep_1(X4,X2,X3)) | ~m1_pre_topc(k2_tsep_1(X4,X2,X3),X5) | v2_struct_0(X5) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X4) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3) | ~m1_pre_topc(X3,X4))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_179])])).
% 3.92/0.95  fof(f1614,plain,(
% 3.92/0.95    ( ! [X4,X2,X5,X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3) | ~m1_pre_topc(X2,X4) | v2_struct_0(X2) | ~m1_pre_topc(X3,X4) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(X4,X2,X3),X5) | v2_struct_0(k2_tsep_1(X4,X2,X3)) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X5,sK1) | ~m1_pre_topc(k2_tsep_1(X4,X2,X3),sK0)) ) | ~spl5_167),
% 3.92/0.95    inference(resolution,[],[f54,f1575])).
% 3.92/0.95  fof(f1645,plain,(
% 3.92/0.95    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_10 | ~spl5_9 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_177 | ~spl5_178 | ~spl5_166),
% 3.92/0.95    inference(avatar_split_clause,[],[f1613,f1555,f1642,f1638,f118,f123,f98,f103,f108,f113,f138,f143,f148])).
% 3.92/0.95  fof(f1638,plain,(
% 3.92/0.95    spl5_177 <=> r1_tsep_1(sK3,sK4)),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).
% 3.92/0.95  fof(f1642,plain,(
% 3.92/0.95    spl5_178 <=> m1_pre_topc(sK3,sK2)),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).
% 3.92/0.95  fof(f1613,plain,(
% 3.92/0.95    ~m1_pre_topc(sK3,sK2) | r1_tsep_1(sK3,sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_166),
% 3.92/0.95    inference(resolution,[],[f54,f1557])).
% 3.92/0.95  fof(f1636,plain,(
% 3.92/0.95    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_14 | ~spl5_13 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_58 | ~spl5_6 | ~spl5_165),
% 3.92/0.95    inference(avatar_split_clause,[],[f1612,f1550,f93,f437,f118,f123,f98,f103,f128,f133,f138,f143,f148])).
% 3.92/0.95  fof(f437,plain,(
% 3.92/0.95    spl5_58 <=> r1_tsep_1(sK1,sK4)),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 3.92/0.95  fof(f1612,plain,(
% 3.92/0.95    ~m1_pre_topc(sK1,sK2) | r1_tsep_1(sK1,sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_165),
% 3.92/0.95    inference(resolution,[],[f54,f1552])).
% 3.92/0.95  fof(f1635,plain,(
% 3.92/0.95    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_19 | ~spl5_22 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_175 | ~spl5_176 | ~spl5_4),
% 3.92/0.95    inference(avatar_split_clause,[],[f1611,f83,f1632,f1628,f118,f123,f98,f103,f200,f178,f138,f143,f148])).
% 3.92/0.95  fof(f1628,plain,(
% 3.92/0.95    spl5_175 <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).
% 3.92/0.95  fof(f1632,plain,(
% 3.92/0.95    spl5_176 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).
% 3.92/0.95  fof(f1611,plain,(
% 3.92/0.95    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 3.92/0.95    inference(resolution,[],[f54,f85])).
% 3.92/0.95  fof(f1626,plain,(
% 3.92/0.95    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_8 | ~spl5_7 | spl5_12 | ~spl5_11 | spl5_174 | ~spl5_134),
% 3.92/0.95    inference(avatar_split_clause,[],[f1622,f1193,f1624,f118,f123,f98,f103,f138,f143,f148])).
% 3.92/0.95  fof(f1624,plain,(
% 3.92/0.95    spl5_174 <=> ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,sK4))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).
% 3.92/0.95  fof(f1622,plain,(
% 3.92/0.95    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3)) ) | ~spl5_134),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1609])).
% 3.92/0.95  fof(f1609,plain,(
% 3.92/0.95    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_134),
% 3.92/0.95    inference(resolution,[],[f54,f1194])).
% 3.92/0.95  fof(f1608,plain,(
% 3.92/0.95    spl5_18 | spl5_173 | ~spl5_167),
% 3.92/0.95    inference(avatar_split_clause,[],[f1589,f1574,f1606,f174])).
% 3.92/0.95  fof(f1606,plain,(
% 3.92/0.95    spl5_173 <=> ! [X13,X15,X12,X14] : (v2_struct_0(X12) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | v2_struct_0(X14) | ~m1_pre_topc(X14,X15) | ~m1_pre_topc(X13,X15) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X15) | r1_tsep_1(X14,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X14,X13) | ~m1_pre_topc(X13,sK0) | ~m1_pre_topc(X12,sK1) | ~m1_pre_topc(X12,sK0) | v2_struct_0(X13) | ~m1_pre_topc(X13,X12))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).
% 3.92/0.95  fof(f1589,plain,(
% 3.92/0.95    ( ! [X14,X12,X15,X13] : (v2_struct_0(X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X13) | ~m1_pre_topc(X12,sK0) | ~m1_pre_topc(X12,sK1) | ~m1_pre_topc(X13,sK0) | r1_tsep_1(X14,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X14,X13) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X15) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X13,X15) | ~m1_pre_topc(X14,X15) | v2_struct_0(X14) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15) | v2_struct_0(X15)) ) | ~spl5_167),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1588])).
% 3.92/0.95  fof(f1588,plain,(
% 3.92/0.95    ( ! [X14,X12,X15,X13] : (v2_struct_0(X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X13) | ~m1_pre_topc(X12,sK0) | ~m1_pre_topc(X12,sK1) | ~m1_pre_topc(X13,sK0) | r1_tsep_1(X14,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X14,X13) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X15) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X13,X15) | v2_struct_0(X13) | ~m1_pre_topc(X14,X15) | v2_struct_0(X14) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15) | v2_struct_0(X15)) ) | ~spl5_167),
% 3.92/0.95    inference(resolution,[],[f1575,f58])).
% 3.92/0.95  fof(f1604,plain,(
% 3.92/0.95    spl5_18 | spl5_172 | ~spl5_167),
% 3.92/0.95    inference(avatar_split_clause,[],[f1590,f1574,f1602,f174])).
% 3.92/0.95  fof(f1602,plain,(
% 3.92/0.95    spl5_172 <=> ! [X9,X11,X8,X10] : (v2_struct_0(X8) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(X10) | ~m1_pre_topc(X10,X11) | ~m1_pre_topc(X9,X11) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(X10,X9) | ~m1_pre_topc(X9,sK0) | ~m1_pre_topc(X8,sK1) | ~m1_pre_topc(X8,sK0) | v2_struct_0(X9) | ~m1_pre_topc(X9,X8))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).
% 3.92/0.95  fof(f1590,plain,(
% 3.92/0.95    ( ! [X10,X8,X11,X9] : (v2_struct_0(X8) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(X8,sK0) | ~m1_pre_topc(X8,sK1) | ~m1_pre_topc(X9,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(X10,X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X9,X11) | ~m1_pre_topc(X10,X11) | v2_struct_0(X10) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11)) ) | ~spl5_167),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1587])).
% 3.92/0.95  fof(f1587,plain,(
% 3.92/0.95    ( ! [X10,X8,X11,X9] : (v2_struct_0(X8) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(X8,sK0) | ~m1_pre_topc(X8,sK1) | ~m1_pre_topc(X9,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(X10,X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X9,X11) | v2_struct_0(X9) | ~m1_pre_topc(X10,X11) | v2_struct_0(X10) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11)) ) | ~spl5_167),
% 3.92/0.95    inference(resolution,[],[f1575,f59])).
% 3.92/0.95  fof(f1600,plain,(
% 3.92/0.95    spl5_18 | spl5_171 | ~spl5_167),
% 3.92/0.95    inference(avatar_split_clause,[],[f1591,f1574,f1598,f174])).
% 3.92/0.95  fof(f1598,plain,(
% 3.92/0.95    spl5_171 <=> ! [X5,X7,X4,X6] : (v2_struct_0(X4) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X5,X7) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X6,X5) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).
% 3.92/0.95  fof(f1591,plain,(
% 3.92/0.95    ( ! [X6,X4,X7,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(X5,sK0) | r1_tsep_1(X6,X5) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X5,X7) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) ) | ~spl5_167),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1586])).
% 3.92/0.95  fof(f1586,plain,(
% 3.92/0.95    ( ! [X6,X4,X7,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(X5,sK0) | r1_tsep_1(X6,X5) | ~m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X5,X7) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) ) | ~spl5_167),
% 3.92/0.95    inference(resolution,[],[f1575,f60])).
% 3.92/0.95  fof(f1596,plain,(
% 3.92/0.95    spl5_18 | spl5_170 | ~spl5_167),
% 3.92/0.95    inference(avatar_split_clause,[],[f1592,f1574,f1594,f174])).
% 3.92/0.95  fof(f1594,plain,(
% 3.92/0.95    spl5_170 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).
% 3.92/0.95  fof(f1592,plain,(
% 3.92/0.95    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_167),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1585])).
% 3.92/0.95  fof(f1585,plain,(
% 3.92/0.95    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,X3) | v2_struct_0(X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_167),
% 3.92/0.95    inference(resolution,[],[f1575,f61])).
% 3.92/0.95  fof(f1584,plain,(
% 3.92/0.95    spl5_18 | spl5_169 | ~spl5_87),
% 3.92/0.95    inference(avatar_split_clause,[],[f1570,f694,f1582,f174])).
% 3.92/0.95  fof(f1582,plain,(
% 3.92/0.95    spl5_169 <=> ! [X9,X11,X8,X10] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X9) | ~m1_pre_topc(X9,X8) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | ~m1_pre_topc(X10,X11) | r1_tsep_1(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X11,sK1) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).
% 3.92/0.95  fof(f694,plain,(
% 3.92/0.95    spl5_87 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 3.92/0.95  fof(f1570,plain,(
% 3.92/0.95    ( ! [X10,X8,X11,X9] : (v2_struct_0(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X10) | ~m1_pre_topc(X10,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,k1_tsep_1(X8,X9,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X11,sK1) | r1_tsep_1(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X10,X11) | ~m1_pre_topc(X11,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_87),
% 3.92/0.95    inference(resolution,[],[f695,f167])).
% 3.92/0.95  fof(f695,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl5_87),
% 3.92/0.95    inference(avatar_component_clause,[],[f694])).
% 3.92/0.95  fof(f1580,plain,(
% 3.92/0.95    spl5_18 | spl5_168 | ~spl5_87),
% 3.92/0.95    inference(avatar_split_clause,[],[f1569,f694,f1578,f174])).
% 3.92/0.95  fof(f1578,plain,(
% 3.92/0.95    spl5_168 <=> ! [X5,X7,X4,X6] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~m1_pre_topc(X6,X7) | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_168])])).
% 3.92/0.95  fof(f1569,plain,(
% 3.92/0.95    ( ! [X6,X4,X7,X5] : (v2_struct_0(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~v2_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~l1_pre_topc(k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | v2_struct_0(X6) | ~m1_pre_topc(X6,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,k1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4),X5)) | ~m1_pre_topc(X7,sK1) | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_87),
% 3.92/0.95    inference(resolution,[],[f695,f50])).
% 3.92/0.95  fof(f1576,plain,(
% 3.92/0.95    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | spl5_167 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_87),
% 3.92/0.95    inference(avatar_split_clause,[],[f1572,f694,f148,f143,f138,f1574,f98,f103,f118,f123])).
% 3.92/0.95  fof(f1572,plain,(
% 3.92/0.95    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK1) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_87),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1567])).
% 3.92/0.95  fof(f1567,plain,(
% 3.92/0.95    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK1) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_87),
% 3.92/0.95    inference(resolution,[],[f695,f68])).
% 3.92/0.95  fof(f1558,plain,(
% 3.92/0.95    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_14 | ~spl5_13 | ~spl5_9 | spl5_166 | spl5_10 | ~spl5_162),
% 3.92/0.95    inference(avatar_split_clause,[],[f1547,f1531,f113,f1555,f108,f128,f133,f138,f143,f148])).
% 3.92/0.95  fof(f1531,plain,(
% 3.92/0.95    spl5_162 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).
% 3.92/0.95  fof(f1547,plain,(
% 3.92/0.95    v2_struct_0(sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_162),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1543])).
% 3.92/0.95  fof(f1543,plain,(
% 3.92/0.95    v2_struct_0(sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_162),
% 3.92/0.95    inference(resolution,[],[f1532,f167])).
% 3.92/0.95  fof(f1532,plain,(
% 3.92/0.95    ( ! [X0] : (~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_162),
% 3.92/0.95    inference(avatar_component_clause,[],[f1531])).
% 3.92/0.95  fof(f1553,plain,(
% 3.92/0.95    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_10 | ~spl5_9 | ~spl5_13 | spl5_165 | spl5_14 | ~spl5_162),
% 3.92/0.95    inference(avatar_split_clause,[],[f1548,f1531,f133,f1550,f128,f108,f113,f138,f143,f148])).
% 3.92/0.95  fof(f1548,plain,(
% 3.92/0.95    v2_struct_0(sK1) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_162),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1542])).
% 3.92/0.95  fof(f1542,plain,(
% 3.92/0.95    v2_struct_0(sK1) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_162),
% 3.92/0.95    inference(resolution,[],[f1532,f50])).
% 3.92/0.95  fof(f1541,plain,(
% 3.92/0.95    spl5_18 | spl5_164 | ~spl5_116),
% 3.92/0.95    inference(avatar_split_clause,[],[f1527,f963,f1539,f174])).
% 3.92/0.95  fof(f1539,plain,(
% 3.92/0.95    spl5_164 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).
% 3.92/0.95  fof(f963,plain,(
% 3.92/0.95    spl5_116 <=> ! [X3,X4] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X3) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X4) | ~m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).
% 3.92/0.95  fof(f1527,plain,(
% 3.92/0.95    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_116),
% 3.92/0.95    inference(resolution,[],[f964,f167])).
% 3.92/0.95  fof(f964,plain,(
% 3.92/0.95    ( ! [X4,X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X3) | ~m1_pre_topc(X3,X4) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X4) | ~m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3))) ) | ~spl5_116),
% 3.92/0.95    inference(avatar_component_clause,[],[f963])).
% 3.92/0.95  fof(f1537,plain,(
% 3.92/0.95    spl5_18 | spl5_163 | ~spl5_116),
% 3.92/0.95    inference(avatar_split_clause,[],[f1526,f963,f1535,f174])).
% 3.92/0.95  fof(f1535,plain,(
% 3.92/0.95    spl5_163 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).
% 3.92/0.95  fof(f1526,plain,(
% 3.92/0.95    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_116),
% 3.92/0.95    inference(resolution,[],[f964,f50])).
% 3.92/0.95  fof(f1533,plain,(
% 3.92/0.95    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_22 | spl5_162 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_116),
% 3.92/0.95    inference(avatar_split_clause,[],[f1529,f963,f148,f143,f138,f1531,f200,f98,f103,f118,f123])).
% 3.92/0.95  fof(f1529,plain,(
% 3.92/0.95    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_116),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1524])).
% 3.92/0.95  fof(f1524,plain,(
% 3.92/0.95    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_116),
% 3.92/0.95    inference(resolution,[],[f964,f68])).
% 3.92/0.95  fof(f1502,plain,(
% 3.92/0.95    spl5_18 | spl5_161 | ~spl5_118),
% 3.92/0.95    inference(avatar_split_clause,[],[f1488,f972,f1500,f174])).
% 3.92/0.95  fof(f1500,plain,(
% 3.92/0.95    spl5_161 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(sK3,X7) | ~m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).
% 3.92/0.95  fof(f972,plain,(
% 3.92/0.95    spl5_118 <=> ! [X9,X10] : (r1_tsep_1(sK3,X9) | v2_struct_0(X10) | ~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(X9) | ~m1_pre_topc(X9,X10) | ~m1_pre_topc(sK3,X10) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | ~m1_pre_topc(X9,k2_tsep_1(sK0,sK2,sK4)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 3.92/0.95  fof(f1488,plain,(
% 3.92/0.95    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(sK3,X7) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_118),
% 3.92/0.95    inference(resolution,[],[f973,f167])).
% 3.92/0.95  fof(f973,plain,(
% 3.92/0.95    ( ! [X10,X9] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | v2_struct_0(X10) | ~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(X9) | ~m1_pre_topc(X9,X10) | ~m1_pre_topc(sK3,X10) | r1_tsep_1(sK3,X9) | ~m1_pre_topc(X9,k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_118),
% 3.92/0.95    inference(avatar_component_clause,[],[f972])).
% 3.92/0.95  fof(f1498,plain,(
% 3.92/0.95    spl5_18 | spl5_160 | ~spl5_118),
% 3.92/0.95    inference(avatar_split_clause,[],[f1487,f972,f1496,f174])).
% 3.92/0.95  fof(f1496,plain,(
% 3.92/0.95    spl5_160 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(sK3,X4) | ~m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).
% 3.92/0.95  fof(f1487,plain,(
% 3.92/0.95    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(sK3,X4) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_118),
% 3.92/0.95    inference(resolution,[],[f973,f50])).
% 3.92/0.95  fof(f1494,plain,(
% 3.92/0.95    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_9 | spl5_159 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_118),
% 3.92/0.95    inference(avatar_split_clause,[],[f1490,f972,f148,f143,f138,f1492,f108,f98,f103,f118,f123])).
% 3.92/0.95  fof(f1492,plain,(
% 3.92/0.95    spl5_159 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(sK3,X0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).
% 3.92/0.95  fof(f1490,plain,(
% 3.92/0.95    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_118),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1485])).
% 3.92/0.95  fof(f1485,plain,(
% 3.92/0.95    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_118),
% 3.92/0.95    inference(resolution,[],[f973,f68])).
% 3.92/0.95  fof(f1481,plain,(
% 3.92/0.95    spl5_18 | spl5_158 | ~spl5_117),
% 3.92/0.95    inference(avatar_split_clause,[],[f1467,f968,f1479,f174])).
% 3.92/0.95  fof(f1479,plain,(
% 3.92/0.95    spl5_158 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(sK1,X7) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).
% 3.92/0.95  fof(f968,plain,(
% 3.92/0.95    spl5_117 <=> ! [X7,X8] : (r1_tsep_1(sK1,X7) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(X7) | ~m1_pre_topc(X7,X8) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).
% 3.92/0.95  fof(f1467,plain,(
% 3.92/0.95    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(sK1,X7) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_117),
% 3.92/0.95    inference(resolution,[],[f969,f167])).
% 3.92/0.95  fof(f969,plain,(
% 3.92/0.95    ( ! [X8,X7] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(X7) | ~m1_pre_topc(X7,X8) | ~m1_pre_topc(sK1,X8) | r1_tsep_1(sK1,X7) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_117),
% 3.92/0.95    inference(avatar_component_clause,[],[f968])).
% 3.92/0.95  fof(f1477,plain,(
% 3.92/0.95    spl5_18 | spl5_157 | ~spl5_117),
% 3.92/0.95    inference(avatar_split_clause,[],[f1466,f968,f1475,f174])).
% 3.92/0.95  fof(f1475,plain,(
% 3.92/0.95    spl5_157 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(sK1,X4) | ~m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).
% 3.92/0.95  fof(f1466,plain,(
% 3.92/0.95    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(sK1,X4) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_117),
% 3.92/0.95    inference(resolution,[],[f969,f50])).
% 3.92/0.95  fof(f1473,plain,(
% 3.92/0.95    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_13 | spl5_156 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_117),
% 3.92/0.95    inference(avatar_split_clause,[],[f1469,f968,f148,f143,f138,f1471,f128,f98,f103,f118,f123])).
% 3.92/0.95  fof(f1471,plain,(
% 3.92/0.95    spl5_156 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).
% 3.92/0.95  fof(f1469,plain,(
% 3.92/0.95    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_117),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1464])).
% 3.92/0.95  fof(f1464,plain,(
% 3.92/0.95    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_117),
% 3.92/0.95    inference(resolution,[],[f969,f68])).
% 3.92/0.95  fof(f1455,plain,(
% 3.92/0.95    spl5_18 | spl5_155 | ~spl5_67),
% 3.92/0.95    inference(avatar_split_clause,[],[f1441,f492,f1453,f174])).
% 3.92/0.95  fof(f1453,plain,(
% 3.92/0.95    spl5_155 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).
% 3.92/0.95  fof(f492,plain,(
% 3.92/0.95    spl5_67 <=> ! [X5,X4] : (r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | ~m1_pre_topc(sK3,X5) | ~m1_pre_topc(X4,sK3))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 3.92/0.95  fof(f1441,plain,(
% 3.92/0.95    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_67),
% 3.92/0.95    inference(resolution,[],[f493,f167])).
% 3.92/0.95  fof(f493,plain,(
% 3.92/0.95    ( ! [X4,X5] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,X5) | ~m1_pre_topc(X4,sK3)) ) | ~spl5_67),
% 3.92/0.95    inference(avatar_component_clause,[],[f492])).
% 3.92/0.95  fof(f1451,plain,(
% 3.92/0.95    spl5_18 | spl5_154 | ~spl5_67),
% 3.92/0.95    inference(avatar_split_clause,[],[f1440,f492,f1449,f174])).
% 3.92/0.95  fof(f1449,plain,(
% 3.92/0.95    spl5_154 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).
% 3.92/0.95  fof(f1440,plain,(
% 3.92/0.95    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_67),
% 3.92/0.95    inference(resolution,[],[f493,f50])).
% 3.92/0.95  fof(f1447,plain,(
% 3.92/0.95    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_9 | spl5_153 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_67),
% 3.92/0.95    inference(avatar_split_clause,[],[f1443,f492,f148,f143,f138,f1445,f108,f98,f103,f118,f123])).
% 3.92/0.95  fof(f1443,plain,(
% 3.92/0.95    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_67),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1438])).
% 3.92/0.95  fof(f1438,plain,(
% 3.92/0.95    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_67),
% 3.92/0.95    inference(resolution,[],[f493,f68])).
% 3.92/0.95  fof(f1422,plain,(
% 3.92/0.95    spl5_10 | spl5_152 | ~spl5_119),
% 3.92/0.95    inference(avatar_split_clause,[],[f1409,f976,f1420,f113])).
% 3.92/0.95  fof(f1420,plain,(
% 3.92/0.95    spl5_152 <=> ! [X7,X8,X6] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X8,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(sK3,X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).
% 3.92/0.95  fof(f976,plain,(
% 3.92/0.95    spl5_119 <=> ! [X11,X12] : (r1_tsep_1(sK3,X11) | v2_struct_0(X12) | ~v2_pre_topc(X12) | ~l1_pre_topc(X12) | v2_struct_0(X11) | ~m1_pre_topc(X11,X12) | ~m1_pre_topc(sK3,X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X11,sK1))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).
% 3.92/0.95  fof(f1409,plain,(
% 3.92/0.95    ( ! [X6,X8,X7] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(sK3,X8) | ~m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(X8,sK1) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_119),
% 3.92/0.95    inference(resolution,[],[f977,f167])).
% 3.92/0.95  fof(f977,plain,(
% 3.92/0.95    ( ! [X12,X11] : (~m1_pre_topc(sK3,X12) | v2_struct_0(X12) | ~v2_pre_topc(X12) | ~l1_pre_topc(X12) | v2_struct_0(X11) | ~m1_pre_topc(X11,X12) | r1_tsep_1(sK3,X11) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X11,sK1)) ) | ~spl5_119),
% 3.92/0.95    inference(avatar_component_clause,[],[f976])).
% 3.92/0.95  fof(f1418,plain,(
% 3.92/0.95    spl5_10 | spl5_151 | ~spl5_119),
% 3.92/0.95    inference(avatar_split_clause,[],[f1408,f976,f1416,f113])).
% 3.92/0.95  fof(f1416,plain,(
% 3.92/0.95    spl5_151 <=> ! [X3,X5,X4] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X5,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(sK3,X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).
% 3.92/0.95  fof(f1408,plain,(
% 3.92/0.95    ( ! [X4,X5,X3] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(sK3,X5) | ~m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(X5,sK1) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_119),
% 3.92/0.95    inference(resolution,[],[f977,f50])).
% 3.92/0.95  fof(f1414,plain,(
% 3.92/0.95    ~spl5_13 | spl5_150 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_9 | ~spl5_119),
% 3.92/0.95    inference(avatar_split_clause,[],[f1406,f976,f108,f148,f143,f138,f1412,f128])).
% 3.92/0.95  fof(f1412,plain,(
% 3.92/0.95    spl5_150 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | r1_tsep_1(sK3,X1) | ~m1_pre_topc(X1,sK0))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).
% 3.92/0.95  fof(f1406,plain,(
% 3.92/0.95    ( ! [X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(sK3,X1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X1,sK1)) ) | (~spl5_9 | ~spl5_119)),
% 3.92/0.95    inference(resolution,[],[f977,f110])).
% 3.92/0.95  fof(f1401,plain,(
% 3.92/0.95    spl5_10 | spl5_149 | ~spl5_86),
% 3.92/0.95    inference(avatar_split_clause,[],[f1388,f676,f1399,f113])).
% 3.92/0.95  fof(f1399,plain,(
% 3.92/0.95    spl5_149 <=> ! [X7,X8,X6] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X8,sK3) | r1_tsep_1(X8,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).
% 3.92/0.95  fof(f676,plain,(
% 3.92/0.95    spl5_86 <=> ! [X5,X4] : (r1_tsep_1(X4,sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(sK1,X5) | ~m1_pre_topc(sK3,X5) | ~m1_pre_topc(X4,sK3))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 3.92/0.95  fof(f1388,plain,(
% 3.92/0.95    ( ! [X6,X8,X7] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(X8,sK1) | ~m1_pre_topc(X8,sK3) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_86),
% 3.92/0.95    inference(resolution,[],[f677,f167])).
% 3.92/0.95  fof(f677,plain,(
% 3.92/0.95    ( ! [X4,X5] : (~m1_pre_topc(sK3,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(sK1,X5) | r1_tsep_1(X4,sK1) | ~m1_pre_topc(X4,sK3)) ) | ~spl5_86),
% 3.92/0.95    inference(avatar_component_clause,[],[f676])).
% 3.92/0.95  fof(f1397,plain,(
% 3.92/0.95    spl5_10 | spl5_148 | ~spl5_86),
% 3.92/0.95    inference(avatar_split_clause,[],[f1387,f676,f1395,f113])).
% 3.92/0.95  fof(f1395,plain,(
% 3.92/0.95    spl5_148 <=> ! [X3,X5,X4] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X5,sK3) | r1_tsep_1(X5,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).
% 3.92/0.95  fof(f1387,plain,(
% 3.92/0.95    ( ! [X4,X5,X3] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(X5,sK1) | ~m1_pre_topc(X5,sK3) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_86),
% 3.92/0.95    inference(resolution,[],[f677,f50])).
% 3.92/0.95  fof(f1393,plain,(
% 3.92/0.95    ~spl5_13 | spl5_147 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_9 | ~spl5_86),
% 3.92/0.95    inference(avatar_split_clause,[],[f1385,f676,f108,f148,f143,f138,f1391,f128])).
% 3.92/0.95  fof(f1391,plain,(
% 3.92/0.95    spl5_147 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X1,sK1) | ~m1_pre_topc(X1,sK0))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).
% 3.92/0.95  fof(f1385,plain,(
% 3.92/0.95    ( ! [X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(sK1,sK0) | r1_tsep_1(X1,sK1) | ~m1_pre_topc(X1,sK3)) ) | (~spl5_9 | ~spl5_86)),
% 3.92/0.95    inference(resolution,[],[f677,f110])).
% 3.92/0.95  fof(f1348,plain,(
% 3.92/0.95    ~spl5_9 | spl5_1 | spl5_10 | ~spl5_5 | ~spl5_140),
% 3.92/0.95    inference(avatar_split_clause,[],[f1347,f1295,f88,f113,f70,f108])).
% 3.92/0.95  fof(f1295,plain,(
% 3.92/0.95    spl5_140 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK4) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).
% 3.92/0.95  fof(f1347,plain,(
% 3.92/0.95    v2_struct_0(sK3) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | (~spl5_5 | ~spl5_140)),
% 3.92/0.95    inference(resolution,[],[f1296,f90])).
% 3.92/0.95  fof(f90,plain,(
% 3.92/0.95    m1_pre_topc(sK3,sK4) | ~spl5_5),
% 3.92/0.95    inference(avatar_component_clause,[],[f88])).
% 3.92/0.95  fof(f1296,plain,(
% 3.92/0.95    ( ! [X0] : (~m1_pre_topc(X0,sK4) | v2_struct_0(X0) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_140),
% 3.92/0.95    inference(avatar_component_clause,[],[f1295])).
% 3.92/0.95  fof(f1337,plain,(
% 3.92/0.95    spl5_18 | spl5_146 | ~spl5_134),
% 3.92/0.95    inference(avatar_split_clause,[],[f1318,f1193,f1335,f174])).
% 3.92/0.95  fof(f1318,plain,(
% 3.92/0.95    ( ! [X10,X11,X9] : (~m1_pre_topc(X9,sK3) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | r1_tsep_1(X10,X9) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X9,X11) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X10,X11) | v2_struct_0(X10) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11)) ) | ~spl5_134),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1317])).
% 3.92/0.95  fof(f1317,plain,(
% 3.92/0.95    ( ! [X10,X11,X9] : (~m1_pre_topc(X9,sK3) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | r1_tsep_1(X10,X9) | ~m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X9,X11) | v2_struct_0(X9) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X10,X11) | v2_struct_0(X10) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11)) ) | ~spl5_134),
% 3.92/0.95    inference(resolution,[],[f1194,f58])).
% 3.92/0.95  fof(f1333,plain,(
% 3.92/0.95    spl5_18 | spl5_145 | ~spl5_134),
% 3.92/0.95    inference(avatar_split_clause,[],[f1319,f1193,f1331,f174])).
% 3.92/0.95  fof(f1319,plain,(
% 3.92/0.95    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK3) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | r1_tsep_1(X6,X7) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_134),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1316])).
% 3.92/0.95  fof(f1316,plain,(
% 3.92/0.95    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK3) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | r1_tsep_1(X6,X7) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X8) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_134),
% 3.92/0.95    inference(resolution,[],[f1194,f59])).
% 3.92/0.95  fof(f1329,plain,(
% 3.92/0.95    spl5_18 | spl5_144 | ~spl5_134),
% 3.92/0.95    inference(avatar_split_clause,[],[f1320,f1193,f1327,f174])).
% 3.92/0.95  fof(f1320,plain,(
% 3.92/0.95    ( ! [X4,X5,X3] : (~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_134),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1315])).
% 3.92/0.95  fof(f1315,plain,(
% 3.92/0.95    ( ! [X4,X5,X3] : (~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_134),
% 3.92/0.95    inference(resolution,[],[f1194,f60])).
% 3.92/0.95  fof(f1325,plain,(
% 3.92/0.95    spl5_18 | spl5_143 | ~spl5_134),
% 3.92/0.95    inference(avatar_split_clause,[],[f1321,f1193,f1323,f174])).
% 3.92/0.95  fof(f1321,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_134),
% 3.92/0.95    inference(duplicate_literal_removal,[],[f1314])).
% 3.92/0.95  fof(f1314,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_134),
% 3.92/0.95    inference(resolution,[],[f1194,f61])).
% 3.92/0.95  fof(f1305,plain,(
% 3.92/0.95    spl5_8 | spl5_142 | ~spl5_123),
% 3.92/0.95    inference(avatar_split_clause,[],[f1292,f1039,f1303,f103])).
% 3.92/0.95  fof(f1303,plain,(
% 3.92/0.95    spl5_142 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK4) | r1_tsep_1(sK2,X7) | ~m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).
% 3.92/0.95  fof(f1039,plain,(
% 3.92/0.95    spl5_123 <=> ! [X1,X0] : (r1_tsep_1(sK2,X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(sK4,X1) | ~m1_pre_topc(X0,sK4))),
% 3.92/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 3.92/0.95  fof(f1292,plain,(
% 3.92/0.95    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(sK2,X7) | ~m1_pre_topc(X7,sK4) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_123),
% 3.92/0.95    inference(resolution,[],[f1040,f167])).
% 3.92/0.95  fof(f1040,plain,(
% 3.92/0.95    ( ! [X0,X1] : (~m1_pre_topc(sK4,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK4)) ) | ~spl5_123),
% 3.92/0.95    inference(avatar_component_clause,[],[f1039])).
% 3.92/0.95  fof(f1301,plain,(
% 3.92/0.95    spl5_8 | spl5_141 | ~spl5_123),
% 3.92/0.95    inference(avatar_split_clause,[],[f1291,f1039,f1299,f103])).
% 4.62/0.96  fof(f1299,plain,(
% 4.62/0.96    spl5_141 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK4) | r1_tsep_1(sK2,X4) | ~m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).
% 4.62/0.96  fof(f1291,plain,(
% 4.62/0.96    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(sK2,X4) | ~m1_pre_topc(X4,sK4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_123),
% 4.62/0.96    inference(resolution,[],[f1040,f50])).
% 4.62/0.96  fof(f1297,plain,(
% 4.62/0.96    ~spl5_11 | spl5_140 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_7 | ~spl5_123),
% 4.62/0.96    inference(avatar_split_clause,[],[f1289,f1039,f98,f148,f143,f138,f1295,f118])).
% 4.62/0.96  fof(f1289,plain,(
% 4.62/0.96    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK4)) ) | (~spl5_7 | ~spl5_123)),
% 4.62/0.96    inference(resolution,[],[f1040,f100])).
% 4.62/0.96  fof(f100,plain,(
% 4.62/0.96    m1_pre_topc(sK4,sK0) | ~spl5_7),
% 4.62/0.96    inference(avatar_component_clause,[],[f98])).
% 4.62/0.96  fof(f1268,plain,(
% 4.62/0.96    spl5_10 | ~spl5_102 | spl5_139 | ~spl5_131),
% 4.62/0.96    inference(avatar_split_clause,[],[f1260,f1153,f1266,f832,f113])).
% 4.62/0.96  fof(f832,plain,(
% 4.62/0.96    spl5_102 <=> l1_pre_topc(sK3)),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 4.62/0.96  fof(f1266,plain,(
% 4.62/0.96    spl5_139 <=> ! [X3,X2] : (v2_struct_0(k2_tsep_1(sK3,X2,X3)) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | ~m1_pre_topc(k2_tsep_1(sK3,X2,X3),sK0) | r1_tsep_1(sK1,k2_tsep_1(sK3,X2,X3)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).
% 4.62/0.96  fof(f1153,plain,(
% 4.62/0.96    spl5_131 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(sK1,X1) | ~m1_pre_topc(X1,sK0))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).
% 4.62/0.96  fof(f1260,plain,(
% 4.62/0.96    ( ! [X2,X3] : (v2_struct_0(k2_tsep_1(sK3,X2,X3)) | r1_tsep_1(sK1,k2_tsep_1(sK3,X2,X3)) | ~m1_pre_topc(k2_tsep_1(sK3,X2,X3),sK0) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X2) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl5_131),
% 4.62/0.96    inference(resolution,[],[f1154,f68])).
% 4.62/0.96  fof(f1154,plain,(
% 4.62/0.96    ( ! [X1] : (~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tsep_1(sK1,X1) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_131),
% 4.62/0.96    inference(avatar_component_clause,[],[f1153])).
% 4.62/0.96  fof(f1264,plain,(
% 4.62/0.96    spl5_10 | ~spl5_102 | spl5_138 | ~spl5_131),
% 4.62/0.96    inference(avatar_split_clause,[],[f1259,f1153,f1262,f832,f113])).
% 4.62/0.96  fof(f1262,plain,(
% 4.62/0.96    spl5_138 <=> ! [X1,X0] : (v2_struct_0(k1_tsep_1(sK3,X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(k1_tsep_1(sK3,X0,X1),sK0) | r1_tsep_1(sK1,k1_tsep_1(sK3,X0,X1)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).
% 4.62/0.96  fof(f1259,plain,(
% 4.62/0.96    ( ! [X0,X1] : (v2_struct_0(k1_tsep_1(sK3,X0,X1)) | r1_tsep_1(sK1,k1_tsep_1(sK3,X0,X1)) | ~m1_pre_topc(k1_tsep_1(sK3,X0,X1),sK0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl5_131),
% 4.62/0.96    inference(resolution,[],[f1154,f65])).
% 4.62/0.96  fof(f65,plain,(
% 4.62/0.96    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.62/0.96    inference(cnf_transformation,[],[f25])).
% 4.62/0.96  fof(f25,plain,(
% 4.62/0.96    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.62/0.96    inference(flattening,[],[f24])).
% 4.62/0.96  fof(f24,plain,(
% 4.62/0.96    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.62/0.96    inference(ennf_transformation,[],[f2])).
% 4.62/0.96  fof(f2,axiom,(
% 4.62/0.96    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 4.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 4.62/0.96  fof(f1233,plain,(
% 4.62/0.96    ~spl5_9 | spl5_10 | ~spl5_137 | spl5_50 | ~spl5_106),
% 4.62/0.96    inference(avatar_split_clause,[],[f1228,f867,f396,f1230,f113,f108])).
% 4.62/0.96  fof(f1230,plain,(
% 4.62/0.96    spl5_137 <=> m1_pre_topc(sK3,sK1)),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).
% 4.62/0.96  fof(f396,plain,(
% 4.62/0.96    spl5_50 <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 4.62/0.96  fof(f1228,plain,(
% 4.62/0.96    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | (spl5_50 | ~spl5_106)),
% 4.62/0.96    inference(resolution,[],[f397,f868])).
% 4.62/0.96  fof(f397,plain,(
% 4.62/0.96    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4)) | spl5_50),
% 4.62/0.96    inference(avatar_component_clause,[],[f396])).
% 4.62/0.96  fof(f1203,plain,(
% 4.62/0.96    spl5_18 | spl5_136 | ~spl5_66),
% 4.62/0.96    inference(avatar_split_clause,[],[f1189,f488,f1201,f174])).
% 4.62/0.96  fof(f1201,plain,(
% 4.62/0.96    spl5_136 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).
% 4.62/0.96  fof(f488,plain,(
% 4.62/0.96    spl5_66 <=> ! [X3,X2] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(X2,sK3))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 4.62/0.96  fof(f1189,plain,(
% 4.62/0.96    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_66),
% 4.62/0.96    inference(resolution,[],[f489,f167])).
% 4.62/0.96  fof(f489,plain,(
% 4.62/0.96    ( ! [X2,X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(X2,sK3)) ) | ~spl5_66),
% 4.62/0.96    inference(avatar_component_clause,[],[f488])).
% 4.62/0.96  fof(f1199,plain,(
% 4.62/0.96    spl5_18 | spl5_135 | ~spl5_66),
% 4.62/0.96    inference(avatar_split_clause,[],[f1188,f488,f1197,f174])).
% 4.62/0.96  fof(f1197,plain,(
% 4.62/0.96    spl5_135 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).
% 4.62/0.96  fof(f1188,plain,(
% 4.62/0.96    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_66),
% 4.62/0.96    inference(resolution,[],[f489,f50])).
% 4.62/0.96  fof(f1195,plain,(
% 4.62/0.96    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_9 | spl5_134 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_66),
% 4.62/0.96    inference(avatar_split_clause,[],[f1191,f488,f148,f143,f138,f1193,f108,f98,f103,f118,f123])).
% 4.62/0.96  fof(f1191,plain,(
% 4.62/0.96    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_66),
% 4.62/0.96    inference(duplicate_literal_removal,[],[f1186])).
% 4.62/0.96  fof(f1186,plain,(
% 4.62/0.96    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_66),
% 4.62/0.96    inference(resolution,[],[f489,f68])).
% 4.62/0.96  fof(f1167,plain,(
% 4.62/0.96    spl5_14 | spl5_10 | spl5_119 | ~spl5_111),
% 4.62/0.96    inference(avatar_split_clause,[],[f1068,f924,f976,f113,f133])).
% 4.62/0.96  fof(f924,plain,(
% 4.62/0.96    spl5_111 <=> r1_tsep_1(sK1,sK3)),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).
% 4.62/0.96  fof(f1068,plain,(
% 4.62/0.96    ( ! [X4,X5] : (r1_tsep_1(sK3,X4) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(sK3,X5) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK1) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_111),
% 4.62/0.96    inference(resolution,[],[f926,f59])).
% 4.62/0.96  fof(f926,plain,(
% 4.62/0.96    r1_tsep_1(sK1,sK3) | ~spl5_111),
% 4.62/0.96    inference(avatar_component_clause,[],[f924])).
% 4.62/0.96  fof(f1166,plain,(
% 4.62/0.96    spl5_10 | spl5_14 | spl5_86 | ~spl5_111),
% 4.62/0.96    inference(avatar_split_clause,[],[f1067,f924,f676,f133,f113])).
% 4.62/0.96  fof(f1067,plain,(
% 4.62/0.96    ( ! [X2,X3] : (r1_tsep_1(X2,sK1) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(sK1,X3) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_111),
% 4.62/0.96    inference(resolution,[],[f926,f60])).
% 4.62/0.96  fof(f1165,plain,(
% 4.62/0.96    spl5_10 | spl5_14 | spl5_85 | ~spl5_111),
% 4.62/0.96    inference(avatar_split_clause,[],[f1066,f924,f672,f133,f113])).
% 4.62/0.96  fof(f672,plain,(
% 4.62/0.96    spl5_85 <=> ! [X3,X2] : (r1_tsep_1(sK1,X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(sK1,X3) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(X2,sK3))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 4.62/0.96  fof(f1066,plain,(
% 4.62/0.96    ( ! [X0,X1] : (r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_111),
% 4.62/0.96    inference(resolution,[],[f926,f61])).
% 4.62/0.96  fof(f1164,plain,(
% 4.62/0.96    spl5_14 | spl5_10 | spl5_84 | ~spl5_111),
% 4.62/0.96    inference(avatar_split_clause,[],[f1069,f924,f668,f113,f133])).
% 4.62/0.96  fof(f668,plain,(
% 4.62/0.96    spl5_84 <=> ! [X1,X0] : (r1_tsep_1(X0,sK3) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(sK1,X1) | ~m1_pre_topc(X0,sK1))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 4.62/0.96  fof(f1069,plain,(
% 4.62/0.96    ( ! [X6,X7] : (r1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK1) | ~m1_pre_topc(sK3,X7) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,X7) | v2_struct_0(sK1) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) ) | ~spl5_111),
% 4.62/0.96    inference(resolution,[],[f926,f58])).
% 4.62/0.96  fof(f1163,plain,(
% 4.62/0.96    spl5_10 | spl5_133 | ~spl5_85),
% 4.62/0.96    inference(avatar_split_clause,[],[f1150,f672,f1161,f113])).
% 4.62/0.96  fof(f1161,plain,(
% 4.62/0.96    spl5_133 <=> ! [X7,X8,X6] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X8,sK3) | r1_tsep_1(sK1,X8) | ~m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).
% 4.62/0.96  fof(f1150,plain,(
% 4.62/0.96    ( ! [X6,X8,X7] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(sK1,X8) | ~m1_pre_topc(X8,sK3) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_85),
% 4.62/0.96    inference(resolution,[],[f673,f167])).
% 4.62/0.96  fof(f673,plain,(
% 4.62/0.96    ( ! [X2,X3] : (~m1_pre_topc(sK3,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(sK1,X3) | r1_tsep_1(sK1,X2) | ~m1_pre_topc(X2,sK3)) ) | ~spl5_85),
% 4.62/0.96    inference(avatar_component_clause,[],[f672])).
% 4.62/0.96  fof(f1159,plain,(
% 4.62/0.96    spl5_10 | spl5_132 | ~spl5_85),
% 4.62/0.96    inference(avatar_split_clause,[],[f1149,f672,f1157,f113])).
% 4.62/0.96  fof(f1157,plain,(
% 4.62/0.96    spl5_132 <=> ! [X3,X5,X4] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X5,sK3) | r1_tsep_1(sK1,X5) | ~m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).
% 4.62/0.96  fof(f1149,plain,(
% 4.62/0.96    ( ! [X4,X5,X3] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(sK1,X5) | ~m1_pre_topc(X5,sK3) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_85),
% 4.62/0.96    inference(resolution,[],[f673,f50])).
% 4.62/0.96  fof(f1155,plain,(
% 4.62/0.96    ~spl5_13 | spl5_131 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_9 | ~spl5_85),
% 4.62/0.96    inference(avatar_split_clause,[],[f1147,f672,f108,f148,f143,f138,f1153,f128])).
% 4.62/0.96  fof(f1147,plain,(
% 4.62/0.96    ( ! [X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(sK1,sK0) | r1_tsep_1(sK1,X1) | ~m1_pre_topc(X1,sK3)) ) | (~spl5_9 | ~spl5_85)),
% 4.62/0.96    inference(resolution,[],[f673,f110])).
% 4.62/0.96  fof(f1139,plain,(
% 4.62/0.96    spl5_8 | spl5_130 | ~spl5_64),
% 4.62/0.96    inference(avatar_split_clause,[],[f1126,f474,f1137,f103])).
% 4.62/0.96  fof(f1137,plain,(
% 4.62/0.96    spl5_130 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(X7,sK4) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).
% 4.62/0.96  fof(f474,plain,(
% 4.62/0.96    spl5_64 <=> ! [X5,X4] : (r1_tsep_1(X4,sK4) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(sK4,X5) | ~m1_pre_topc(sK1,X5) | ~m1_pre_topc(X4,sK1))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 4.62/0.96  fof(f1126,plain,(
% 4.62/0.96    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(X7,sK4) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_64),
% 4.62/0.96    inference(resolution,[],[f475,f167])).
% 4.62/0.96  fof(f475,plain,(
% 4.62/0.96    ( ! [X4,X5] : (~m1_pre_topc(sK4,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | r1_tsep_1(X4,sK4) | ~m1_pre_topc(sK1,X5) | ~m1_pre_topc(X4,sK1)) ) | ~spl5_64),
% 4.62/0.96    inference(avatar_component_clause,[],[f474])).
% 4.62/0.96  fof(f1135,plain,(
% 4.62/0.96    spl5_8 | spl5_129 | ~spl5_64),
% 4.62/0.96    inference(avatar_split_clause,[],[f1125,f474,f1133,f103])).
% 4.62/0.96  fof(f1133,plain,(
% 4.62/0.96    spl5_129 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(X4,sK4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).
% 4.62/0.96  fof(f1125,plain,(
% 4.62/0.96    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(X4,sK4) | ~m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_64),
% 4.62/0.96    inference(resolution,[],[f475,f50])).
% 4.62/0.96  fof(f1131,plain,(
% 4.62/0.96    ~spl5_13 | spl5_128 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_7 | ~spl5_64),
% 4.62/0.96    inference(avatar_split_clause,[],[f1123,f474,f98,f148,f143,f138,f1129,f128])).
% 4.62/0.96  fof(f1129,plain,(
% 4.62/0.96    spl5_128 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X0,sK4) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).
% 4.62/0.96  fof(f1123,plain,(
% 4.62/0.96    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,sK4) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X0,sK1)) ) | (~spl5_7 | ~spl5_64)),
% 4.62/0.96    inference(resolution,[],[f475,f100])).
% 4.62/0.96  fof(f1065,plain,(
% 4.62/0.96    spl5_10 | spl5_12 | spl5_127 | ~spl5_110),
% 4.62/0.96    inference(avatar_split_clause,[],[f1049,f909,f1063,f123,f113])).
% 4.62/0.96  fof(f1049,plain,(
% 4.62/0.96    ( ! [X6,X7] : (r1_tsep_1(X6,sK2) | ~m1_pre_topc(X6,sK3) | ~m1_pre_topc(sK2,X7) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,X7) | v2_struct_0(sK3) | ~m1_pre_topc(X6,X7) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) ) | ~spl5_110),
% 4.62/0.96    inference(resolution,[],[f911,f58])).
% 4.62/0.96  fof(f911,plain,(
% 4.62/0.96    r1_tsep_1(sK3,sK2) | ~spl5_110),
% 4.62/0.96    inference(avatar_component_clause,[],[f909])).
% 4.62/0.96  fof(f1061,plain,(
% 4.62/0.96    spl5_10 | spl5_12 | spl5_126 | ~spl5_110),
% 4.62/0.96    inference(avatar_split_clause,[],[f1048,f909,f1059,f123,f113])).
% 4.62/0.96  fof(f1048,plain,(
% 4.62/0.96    ( ! [X4,X5] : (r1_tsep_1(sK2,X4) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(sK2,X5) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,X5) | v2_struct_0(sK3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_110),
% 4.62/0.96    inference(resolution,[],[f911,f59])).
% 4.62/0.96  fof(f1057,plain,(
% 4.62/0.96    spl5_12 | spl5_10 | spl5_125 | ~spl5_110),
% 4.62/0.96    inference(avatar_split_clause,[],[f1047,f909,f1055,f113,f123])).
% 4.62/0.96  fof(f1047,plain,(
% 4.62/0.96    ( ! [X2,X3] : (r1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK2) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,X3) | v2_struct_0(sK2) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_110),
% 4.62/0.96    inference(resolution,[],[f911,f60])).
% 4.62/0.96  fof(f1053,plain,(
% 4.62/0.96    spl5_12 | spl5_10 | spl5_124 | ~spl5_110),
% 4.62/0.96    inference(avatar_split_clause,[],[f1046,f909,f1051,f113,f123])).
% 4.62/0.96  fof(f1046,plain,(
% 4.62/0.96    ( ! [X0,X1] : (r1_tsep_1(sK3,X0) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_110),
% 4.62/0.96    inference(resolution,[],[f911,f61])).
% 4.62/0.96  fof(f1041,plain,(
% 4.62/0.96    spl5_8 | spl5_12 | spl5_123 | ~spl5_3),
% 4.62/0.96    inference(avatar_split_clause,[],[f1034,f79,f1039,f123,f103])).
% 4.62/0.96  fof(f79,plain,(
% 4.62/0.96    spl5_3 <=> r1_tsep_1(sK2,sK4)),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 4.62/0.96  fof(f1034,plain,(
% 4.62/0.96    ( ! [X0,X1] : (r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK4) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_3),
% 4.62/0.96    inference(resolution,[],[f81,f61])).
% 4.62/0.96  fof(f81,plain,(
% 4.62/0.96    r1_tsep_1(sK2,sK4) | ~spl5_3),
% 4.62/0.96    inference(avatar_component_clause,[],[f79])).
% 4.62/0.96  fof(f1029,plain,(
% 4.62/0.96    spl5_18 | spl5_122 | ~spl5_65),
% 4.62/0.96    inference(avatar_split_clause,[],[f1015,f484,f1027,f174])).
% 4.62/0.96  fof(f1027,plain,(
% 4.62/0.96    spl5_122 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X7,sK3) | ~m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).
% 4.62/0.96  fof(f484,plain,(
% 4.62/0.96    spl5_65 <=> ! [X1,X0] : (r1_tsep_1(X0,sK3) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)))),
% 4.62/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 4.62/0.96  fof(f1015,plain,(
% 4.62/0.96    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(sK3,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,sK3) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_65),
% 4.62/0.96    inference(resolution,[],[f485,f167])).
% 4.62/0.96  fof(f485,plain,(
% 4.62/0.96    ( ! [X0,X1] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_65),
% 4.62/0.96    inference(avatar_component_clause,[],[f484])).
% 4.62/0.96  fof(f1025,plain,(
% 4.62/0.96    spl5_18 | spl5_121 | ~spl5_65),
% 4.62/0.96    inference(avatar_split_clause,[],[f1014,f484,f1023,f174])).
% 4.62/0.96  fof(f1023,plain,(
% 4.62/0.96    spl5_121 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X4,sK3) | ~m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).
% 4.62/0.97  fof(f1014,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(sK3,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,sK3) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_65),
% 4.62/0.97    inference(resolution,[],[f485,f50])).
% 4.62/0.97  fof(f1021,plain,(
% 4.62/0.97    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_9 | spl5_120 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_65),
% 4.62/0.97    inference(avatar_split_clause,[],[f1017,f484,f148,f143,f138,f1019,f108,f98,f103,f118,f123])).
% 4.62/0.97  fof(f1019,plain,(
% 4.62/0.97    spl5_120 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).
% 4.62/0.97  fof(f1017,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_65),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f1012])).
% 4.62/0.97  fof(f1012,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_65),
% 4.62/0.97    inference(resolution,[],[f485,f68])).
% 4.62/0.97  fof(f978,plain,(
% 4.62/0.97    spl5_14 | spl5_10 | spl5_119 | ~spl5_80),
% 4.62/0.97    inference(avatar_split_clause,[],[f956,f617,f976,f113,f133])).
% 4.62/0.97  fof(f617,plain,(
% 4.62/0.97    spl5_80 <=> r1_tsep_1(sK3,sK1)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 4.62/0.97  fof(f956,plain,(
% 4.62/0.97    ( ! [X12,X11] : (r1_tsep_1(sK3,X11) | ~m1_pre_topc(X11,sK1) | ~m1_pre_topc(sK3,X12) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,X12) | v2_struct_0(sK1) | ~m1_pre_topc(X11,X12) | v2_struct_0(X11) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12)) ) | ~spl5_80),
% 4.62/0.97    inference(resolution,[],[f61,f619])).
% 4.62/0.97  fof(f619,plain,(
% 4.62/0.97    r1_tsep_1(sK3,sK1) | ~spl5_80),
% 4.62/0.97    inference(avatar_component_clause,[],[f617])).
% 4.62/0.97  fof(f974,plain,(
% 4.62/0.97    spl5_18 | spl5_10 | spl5_118 | ~spl5_50),
% 4.62/0.97    inference(avatar_split_clause,[],[f955,f396,f972,f113,f174])).
% 4.62/0.97  fof(f955,plain,(
% 4.62/0.97    ( ! [X10,X9] : (r1_tsep_1(sK3,X9) | ~m1_pre_topc(X9,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,X10) | v2_struct_0(sK3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X10) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X9,X10) | v2_struct_0(X9) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10)) ) | ~spl5_50),
% 4.62/0.97    inference(resolution,[],[f61,f398])).
% 4.62/0.97  fof(f398,plain,(
% 4.62/0.97    r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4)) | ~spl5_50),
% 4.62/0.97    inference(avatar_component_clause,[],[f396])).
% 4.62/0.97  fof(f970,plain,(
% 4.62/0.97    spl5_18 | spl5_14 | spl5_117 | ~spl5_49),
% 4.62/0.97    inference(avatar_split_clause,[],[f954,f391,f968,f133,f174])).
% 4.62/0.97  fof(f391,plain,(
% 4.62/0.97    spl5_49 <=> r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 4.62/0.97  fof(f954,plain,(
% 4.62/0.97    ( ! [X8,X7] : (r1_tsep_1(sK1,X7) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,X8) | v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_49),
% 4.62/0.97    inference(resolution,[],[f61,f393])).
% 4.62/0.97  fof(f393,plain,(
% 4.62/0.97    r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4)) | ~spl5_49),
% 4.62/0.97    inference(avatar_component_clause,[],[f391])).
% 4.62/0.97  fof(f966,plain,(
% 4.62/0.97    spl5_8 | spl5_14 | spl5_77 | ~spl5_58),
% 4.62/0.97    inference(avatar_split_clause,[],[f953,f437,f594,f133,f103])).
% 4.62/0.97  fof(f594,plain,(
% 4.62/0.97    spl5_77 <=> ! [X3,X2] : (r1_tsep_1(sK1,X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(sK1,X3) | ~m1_pre_topc(sK4,X3) | ~m1_pre_topc(X2,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 4.62/0.97  fof(f953,plain,(
% 4.62/0.97    ( ! [X6,X5] : (r1_tsep_1(sK1,X5) | ~m1_pre_topc(X5,sK4) | ~m1_pre_topc(sK1,X6) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,X6) | v2_struct_0(sK4) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_58),
% 4.62/0.97    inference(resolution,[],[f61,f439])).
% 4.62/0.97  fof(f439,plain,(
% 4.62/0.97    r1_tsep_1(sK1,sK4) | ~spl5_58),
% 4.62/0.97    inference(avatar_component_clause,[],[f437])).
% 4.62/0.97  fof(f965,plain,(
% 4.62/0.97    spl5_19 | spl5_18 | spl5_116 | ~spl5_4),
% 4.62/0.97    inference(avatar_split_clause,[],[f952,f83,f963,f174,f178])).
% 4.62/0.97  fof(f952,plain,(
% 4.62/0.97    ( ! [X4,X3] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3) | ~m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X4) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X3,X4) | v2_struct_0(X3) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_4),
% 4.62/0.97    inference(resolution,[],[f61,f85])).
% 4.62/0.97  fof(f961,plain,(
% 4.62/0.97    spl5_18 | spl5_115 | ~spl5_81),
% 4.62/0.97    inference(avatar_split_clause,[],[f957,f644,f959,f174])).
% 4.62/0.97  fof(f957,plain,(
% 4.62/0.97    ( ! [X2,X0,X1] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_81),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f951])).
% 4.62/0.97  fof(f951,plain,(
% 4.62/0.97    ( ! [X2,X0,X1] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_81),
% 4.62/0.97    inference(resolution,[],[f61,f645])).
% 4.62/0.97  fof(f947,plain,(
% 4.62/0.97    spl5_14 | ~spl5_112 | spl5_114 | ~spl5_96),
% 4.62/0.97    inference(avatar_split_clause,[],[f934,f803,f945,f936,f133])).
% 4.62/0.97  fof(f936,plain,(
% 4.62/0.97    spl5_112 <=> l1_pre_topc(sK1)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).
% 4.62/0.97  fof(f945,plain,(
% 4.62/0.97    spl5_114 <=> ! [X3,X2] : (v2_struct_0(k2_tsep_1(sK1,X2,X3)) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK1) | ~m1_pre_topc(k2_tsep_1(sK1,X2,X3),sK0) | r1_tsep_1(sK4,k2_tsep_1(sK1,X2,X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 4.62/0.97  fof(f803,plain,(
% 4.62/0.97    spl5_96 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 4.62/0.97  fof(f934,plain,(
% 4.62/0.97    ( ! [X2,X3] : (v2_struct_0(k2_tsep_1(sK1,X2,X3)) | r1_tsep_1(sK4,k2_tsep_1(sK1,X2,X3)) | ~m1_pre_topc(k2_tsep_1(sK1,X2,X3),sK0) | ~m1_pre_topc(X3,sK1) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_96),
% 4.62/0.97    inference(resolution,[],[f804,f68])).
% 4.62/0.97  fof(f804,plain,(
% 4.62/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_96),
% 4.62/0.97    inference(avatar_component_clause,[],[f803])).
% 4.62/0.97  fof(f943,plain,(
% 4.62/0.97    spl5_14 | ~spl5_112 | spl5_113 | ~spl5_96),
% 4.62/0.97    inference(avatar_split_clause,[],[f933,f803,f941,f936,f133])).
% 4.62/0.97  fof(f941,plain,(
% 4.62/0.97    spl5_113 <=> ! [X1,X0] : (v2_struct_0(k1_tsep_1(sK1,X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(k1_tsep_1(sK1,X0,X1),sK0) | r1_tsep_1(sK4,k1_tsep_1(sK1,X0,X1)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).
% 4.62/0.97  fof(f933,plain,(
% 4.62/0.97    ( ! [X0,X1] : (v2_struct_0(k1_tsep_1(sK1,X0,X1)) | r1_tsep_1(sK4,k1_tsep_1(sK1,X0,X1)) | ~m1_pre_topc(k1_tsep_1(sK1,X0,X1),sK0) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_96),
% 4.62/0.97    inference(resolution,[],[f804,f65])).
% 4.62/0.97  fof(f939,plain,(
% 4.62/0.97    ~spl5_112 | ~spl5_13 | spl5_2 | spl5_14 | ~spl5_96),
% 4.62/0.97    inference(avatar_split_clause,[],[f932,f803,f133,f74,f128,f936])).
% 4.62/0.97  fof(f932,plain,(
% 4.62/0.97    v2_struct_0(sK1) | r1_tsep_1(sK4,sK1) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK1) | ~spl5_96),
% 4.62/0.97    inference(resolution,[],[f804,f49])).
% 4.62/0.97  fof(f49,plain,(
% 4.62/0.97    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 4.62/0.97    inference(cnf_transformation,[],[f13])).
% 4.62/0.97  fof(f13,plain,(
% 4.62/0.97    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 4.62/0.97    inference(ennf_transformation,[],[f7])).
% 4.62/0.97  fof(f7,axiom,(
% 4.62/0.97    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 4.62/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 4.62/0.97  fof(f927,plain,(
% 4.62/0.97    ~spl5_9 | spl5_111 | spl5_10 | ~spl5_5 | ~spl5_93),
% 4.62/0.97    inference(avatar_split_clause,[],[f922,f781,f88,f113,f924,f108])).
% 4.62/0.97  fof(f781,plain,(
% 4.62/0.97    spl5_93 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK4) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 4.62/0.97  fof(f922,plain,(
% 4.62/0.97    v2_struct_0(sK3) | r1_tsep_1(sK1,sK3) | ~m1_pre_topc(sK3,sK0) | (~spl5_5 | ~spl5_93)),
% 4.62/0.97    inference(resolution,[],[f782,f90])).
% 4.62/0.97  fof(f782,plain,(
% 4.62/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK4) | v2_struct_0(X0) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_93),
% 4.62/0.97    inference(avatar_component_clause,[],[f781])).
% 4.62/0.97  fof(f912,plain,(
% 4.62/0.97    ~spl5_9 | spl5_110 | spl5_10 | ~spl5_5 | ~spl5_90),
% 4.62/0.97    inference(avatar_split_clause,[],[f907,f745,f88,f113,f909,f108])).
% 4.62/0.97  fof(f745,plain,(
% 4.62/0.97    spl5_90 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK4) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).
% 4.62/0.97  fof(f907,plain,(
% 4.62/0.97    v2_struct_0(sK3) | r1_tsep_1(sK3,sK2) | ~m1_pre_topc(sK3,sK0) | (~spl5_5 | ~spl5_90)),
% 4.62/0.97    inference(resolution,[],[f746,f90])).
% 4.62/0.97  fof(f746,plain,(
% 4.62/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK4) | v2_struct_0(X0) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_90),
% 4.62/0.97    inference(avatar_component_clause,[],[f745])).
% 4.62/0.97  fof(f895,plain,(
% 4.62/0.97    ~spl5_22 | spl5_19 | ~spl5_109 | spl5_4 | ~spl5_81),
% 4.62/0.97    inference(avatar_split_clause,[],[f890,f644,f83,f892,f178,f200])).
% 4.62/0.97  fof(f892,plain,(
% 4.62/0.97    spl5_109 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK1)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).
% 4.62/0.97  fof(f890,plain,(
% 4.62/0.97    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK1) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | (spl5_4 | ~spl5_81)),
% 4.62/0.97    inference(resolution,[],[f84,f645])).
% 4.62/0.97  fof(f84,plain,(
% 4.62/0.97    ~r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | spl5_4),
% 4.62/0.97    inference(avatar_component_clause,[],[f83])).
% 4.62/0.97  fof(f877,plain,(
% 4.62/0.97    spl5_18 | spl5_108 | ~spl5_61),
% 4.62/0.97    inference(avatar_split_clause,[],[f863,f456,f875,f174])).
% 4.62/0.97  fof(f875,plain,(
% 4.62/0.97    spl5_108 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).
% 4.62/0.97  fof(f456,plain,(
% 4.62/0.97    spl5_61 <=> ! [X5,X4] : (r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | ~m1_pre_topc(sK1,X5) | ~m1_pre_topc(X4,sK1))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 4.62/0.97  fof(f863,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_61),
% 4.62/0.97    inference(resolution,[],[f457,f167])).
% 4.62/0.97  fof(f457,plain,(
% 4.62/0.97    ( ! [X4,X5] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,X5) | ~m1_pre_topc(X4,sK1)) ) | ~spl5_61),
% 4.62/0.97    inference(avatar_component_clause,[],[f456])).
% 4.62/0.97  fof(f873,plain,(
% 4.62/0.97    spl5_18 | spl5_107 | ~spl5_61),
% 4.62/0.97    inference(avatar_split_clause,[],[f862,f456,f871,f174])).
% 4.62/0.97  fof(f871,plain,(
% 4.62/0.97    spl5_107 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 4.62/0.97  fof(f862,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_61),
% 4.62/0.97    inference(resolution,[],[f457,f50])).
% 4.62/0.97  fof(f869,plain,(
% 4.62/0.97    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_13 | spl5_106 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_61),
% 4.62/0.97    inference(avatar_split_clause,[],[f865,f456,f148,f143,f138,f867,f128,f98,f103,f118,f123])).
% 4.62/0.97  fof(f865,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_61),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f860])).
% 4.62/0.97  fof(f860,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_61),
% 4.62/0.97    inference(resolution,[],[f457,f68])).
% 4.62/0.97  fof(f847,plain,(
% 4.62/0.97    spl5_10 | spl5_105 | ~spl5_84),
% 4.62/0.97    inference(avatar_split_clause,[],[f818,f668,f845,f113])).
% 4.62/0.97  fof(f845,plain,(
% 4.62/0.97    spl5_105 <=> ! [X7,X8,X6] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X8,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(X8,sK3) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).
% 4.62/0.97  fof(f818,plain,(
% 4.62/0.97    ( ! [X6,X8,X7] : (v2_struct_0(k1_tsep_1(X6,X7,sK3)) | ~v2_pre_topc(k1_tsep_1(X6,X7,sK3)) | ~l1_pre_topc(k1_tsep_1(X6,X7,sK3)) | v2_struct_0(X8) | ~m1_pre_topc(X8,k1_tsep_1(X6,X7,sK3)) | r1_tsep_1(X8,sK3) | ~m1_pre_topc(sK1,k1_tsep_1(X6,X7,sK3)) | ~m1_pre_topc(X8,sK1) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl5_84),
% 4.62/0.97    inference(resolution,[],[f669,f167])).
% 4.62/0.97  fof(f669,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(sK1,X1) | ~m1_pre_topc(X0,sK1)) ) | ~spl5_84),
% 4.62/0.97    inference(avatar_component_clause,[],[f668])).
% 4.62/0.97  fof(f843,plain,(
% 4.62/0.97    spl5_10 | spl5_104 | ~spl5_84),
% 4.62/0.97    inference(avatar_split_clause,[],[f817,f668,f841,f113])).
% 4.62/0.97  fof(f841,plain,(
% 4.62/0.97    spl5_104 <=> ! [X3,X5,X4] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X4) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X5,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(X5,sK3) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).
% 4.62/0.97  fof(f817,plain,(
% 4.62/0.97    ( ! [X4,X5,X3] : (v2_struct_0(k1_tsep_1(X3,sK3,X4)) | ~v2_pre_topc(k1_tsep_1(X3,sK3,X4)) | ~l1_pre_topc(k1_tsep_1(X3,sK3,X4)) | v2_struct_0(X5) | ~m1_pre_topc(X5,k1_tsep_1(X3,sK3,X4)) | r1_tsep_1(X5,sK3) | ~m1_pre_topc(sK1,k1_tsep_1(X3,sK3,X4)) | ~m1_pre_topc(X5,sK1) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_84),
% 4.62/0.97    inference(resolution,[],[f669,f50])).
% 4.62/0.97  fof(f839,plain,(
% 4.62/0.97    ~spl5_100 | spl5_101 | ~spl5_102 | ~spl5_103 | spl5_10 | ~spl5_84),
% 4.62/0.97    inference(avatar_split_clause,[],[f819,f668,f113,f836,f832,f829,f825])).
% 4.62/0.97  fof(f825,plain,(
% 4.62/0.97    spl5_100 <=> m1_pre_topc(sK1,sK3)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 4.62/0.97  fof(f829,plain,(
% 4.62/0.97    spl5_101 <=> ! [X2] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | r1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).
% 4.62/0.97  fof(f836,plain,(
% 4.62/0.97    spl5_103 <=> v2_pre_topc(sK3)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).
% 4.62/0.97  fof(f819,plain,(
% 4.62/0.97    ( ! [X2] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK3) | r1_tsep_1(X2,sK3) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(X2,sK1)) ) | ~spl5_84),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f816])).
% 4.62/0.97  fof(f816,plain,(
% 4.62/0.97    ( ! [X2] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK3) | r1_tsep_1(X2,sK3) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(X2,sK1) | ~l1_pre_topc(sK3)) ) | ~spl5_84),
% 4.62/0.97    inference(resolution,[],[f669,f49])).
% 4.62/0.97  fof(f823,plain,(
% 4.62/0.97    ~spl5_13 | spl5_99 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_9 | ~spl5_84),
% 4.62/0.97    inference(avatar_split_clause,[],[f815,f668,f108,f148,f143,f138,f821,f128])).
% 4.62/0.97  fof(f821,plain,(
% 4.62/0.97    spl5_99 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | r1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).
% 4.62/0.97  fof(f815,plain,(
% 4.62/0.97    ( ! [X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,sK3) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X1,sK1)) ) | (~spl5_9 | ~spl5_84)),
% 4.62/0.97    inference(resolution,[],[f669,f110])).
% 4.62/0.97  fof(f813,plain,(
% 4.62/0.97    spl5_8 | spl5_98 | ~spl5_63),
% 4.62/0.97    inference(avatar_split_clause,[],[f800,f470,f811,f103])).
% 4.62/0.97  fof(f811,plain,(
% 4.62/0.97    spl5_98 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(sK4,X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 4.62/0.97  fof(f470,plain,(
% 4.62/0.97    spl5_63 <=> ! [X3,X2] : (r1_tsep_1(sK4,X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(sK4,X3) | ~m1_pre_topc(sK1,X3) | ~m1_pre_topc(X2,sK1))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 4.62/0.97  fof(f800,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(sK4,X7) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_63),
% 4.62/0.97    inference(resolution,[],[f471,f167])).
% 4.62/0.97  fof(f471,plain,(
% 4.62/0.97    ( ! [X2,X3] : (~m1_pre_topc(sK4,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(sK4,X2) | ~m1_pre_topc(sK1,X3) | ~m1_pre_topc(X2,sK1)) ) | ~spl5_63),
% 4.62/0.97    inference(avatar_component_clause,[],[f470])).
% 4.62/0.97  fof(f809,plain,(
% 4.62/0.97    spl5_8 | spl5_97 | ~spl5_63),
% 4.62/0.97    inference(avatar_split_clause,[],[f799,f470,f807,f103])).
% 4.62/0.97  fof(f807,plain,(
% 4.62/0.97    spl5_97 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(sK4,X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 4.62/0.97  fof(f799,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(sK4,X4) | ~m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_63),
% 4.62/0.97    inference(resolution,[],[f471,f50])).
% 4.62/0.97  fof(f805,plain,(
% 4.62/0.97    ~spl5_13 | spl5_96 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_7 | ~spl5_63),
% 4.62/0.97    inference(avatar_split_clause,[],[f797,f470,f98,f148,f143,f138,f803,f128])).
% 4.62/0.97  fof(f797,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X0,sK1)) ) | (~spl5_7 | ~spl5_63)),
% 4.62/0.97    inference(resolution,[],[f471,f100])).
% 4.62/0.97  fof(f791,plain,(
% 4.62/0.97    spl5_8 | spl5_95 | ~spl5_77),
% 4.62/0.97    inference(avatar_split_clause,[],[f778,f594,f789,f103])).
% 4.62/0.97  fof(f789,plain,(
% 4.62/0.97    spl5_95 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK4) | r1_tsep_1(sK1,X7) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 4.62/0.97  fof(f778,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(sK1,X7) | ~m1_pre_topc(X7,sK4) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_77),
% 4.62/0.97    inference(resolution,[],[f595,f167])).
% 4.62/0.97  fof(f595,plain,(
% 4.62/0.97    ( ! [X2,X3] : (~m1_pre_topc(sK4,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(sK1,X3) | r1_tsep_1(sK1,X2) | ~m1_pre_topc(X2,sK4)) ) | ~spl5_77),
% 4.62/0.97    inference(avatar_component_clause,[],[f594])).
% 4.62/0.97  fof(f787,plain,(
% 4.62/0.97    spl5_8 | spl5_94 | ~spl5_77),
% 4.62/0.97    inference(avatar_split_clause,[],[f777,f594,f785,f103])).
% 4.62/0.97  fof(f785,plain,(
% 4.62/0.97    spl5_94 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK4) | r1_tsep_1(sK1,X4) | ~m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 4.62/0.97  fof(f777,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(sK1,X4) | ~m1_pre_topc(X4,sK4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_77),
% 4.62/0.97    inference(resolution,[],[f595,f50])).
% 4.62/0.97  fof(f783,plain,(
% 4.62/0.97    ~spl5_13 | spl5_93 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_7 | ~spl5_77),
% 4.62/0.97    inference(avatar_split_clause,[],[f775,f594,f98,f148,f143,f138,f781,f128])).
% 4.62/0.97  fof(f775,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | r1_tsep_1(sK1,X0) | ~m1_pre_topc(X0,sK4)) ) | (~spl5_7 | ~spl5_77)),
% 4.62/0.97    inference(resolution,[],[f595,f100])).
% 4.62/0.97  fof(f755,plain,(
% 4.62/0.97    spl5_8 | spl5_92 | ~spl5_38),
% 4.62/0.97    inference(avatar_split_clause,[],[f742,f308,f753,f103])).
% 4.62/0.97  fof(f753,plain,(
% 4.62/0.97    spl5_92 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK4) | r1_tsep_1(X7,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 4.62/0.97  fof(f308,plain,(
% 4.62/0.97    spl5_38 <=> ! [X1,X0] : (r1_tsep_1(X0,sK2) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(sK4,X1) | ~m1_pre_topc(X0,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 4.62/0.97  fof(f742,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(X7,sK2) | ~m1_pre_topc(X7,sK4) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_38),
% 4.62/0.97    inference(resolution,[],[f309,f167])).
% 4.62/0.97  fof(f309,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(sK4,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK4)) ) | ~spl5_38),
% 4.62/0.97    inference(avatar_component_clause,[],[f308])).
% 4.62/0.97  fof(f751,plain,(
% 4.62/0.97    spl5_8 | spl5_91 | ~spl5_38),
% 4.62/0.97    inference(avatar_split_clause,[],[f741,f308,f749,f103])).
% 4.62/0.97  fof(f749,plain,(
% 4.62/0.97    spl5_91 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK4) | r1_tsep_1(X4,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 4.62/0.97  fof(f741,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(X4,sK2) | ~m1_pre_topc(X4,sK4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_38),
% 4.62/0.97    inference(resolution,[],[f309,f50])).
% 4.62/0.97  fof(f747,plain,(
% 4.62/0.97    ~spl5_11 | spl5_90 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_7 | ~spl5_38),
% 4.62/0.97    inference(avatar_split_clause,[],[f739,f308,f98,f148,f143,f138,f745,f118])).
% 4.62/0.97  fof(f739,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK4)) ) | (~spl5_7 | ~spl5_38)),
% 4.62/0.97    inference(resolution,[],[f309,f100])).
% 4.62/0.97  fof(f704,plain,(
% 4.62/0.97    spl5_18 | spl5_89 | ~spl5_81),
% 4.62/0.97    inference(avatar_split_clause,[],[f690,f644,f702,f174])).
% 4.62/0.97  fof(f690,plain,(
% 4.62/0.97    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK1) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | r1_tsep_1(X7,X6) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X8) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_81),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f689])).
% 4.62/0.97  fof(f689,plain,(
% 4.62/0.97    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK1) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | r1_tsep_1(X7,X6) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X8) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,X8) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) ) | ~spl5_81),
% 4.62/0.97    inference(resolution,[],[f645,f58])).
% 4.62/0.97  fof(f700,plain,(
% 4.62/0.97    spl5_18 | spl5_88 | ~spl5_81),
% 4.62/0.97    inference(avatar_split_clause,[],[f691,f644,f698,f174])).
% 4.62/0.97  fof(f691,plain,(
% 4.62/0.97    ( ! [X4,X5,X3] : (~m1_pre_topc(X3,sK1) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | r1_tsep_1(X3,X4) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_81),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f688])).
% 4.62/0.97  fof(f688,plain,(
% 4.62/0.97    ( ! [X4,X5,X3] : (~m1_pre_topc(X3,sK1) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | r1_tsep_1(X3,X4) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_81),
% 4.62/0.97    inference(resolution,[],[f645,f59])).
% 4.62/0.97  fof(f696,plain,(
% 4.62/0.97    spl5_18 | spl5_87 | ~spl5_81),
% 4.62/0.97    inference(avatar_split_clause,[],[f692,f644,f694,f174])).
% 4.62/0.97  fof(f692,plain,(
% 4.62/0.97    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_81),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f687])).
% 4.62/0.97  fof(f687,plain,(
% 4.62/0.97    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_81),
% 4.62/0.97    inference(resolution,[],[f645,f60])).
% 4.62/0.97  fof(f680,plain,(
% 4.62/0.97    spl5_14 | spl5_8 | spl5_64 | ~spl5_2),
% 4.62/0.97    inference(avatar_split_clause,[],[f655,f74,f474,f103,f133])).
% 4.62/0.97  fof(f655,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,sK4) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_2),
% 4.62/0.97    inference(resolution,[],[f75,f60])).
% 4.62/0.97  fof(f75,plain,(
% 4.62/0.97    r1_tsep_1(sK4,sK1) | ~spl5_2),
% 4.62/0.97    inference(avatar_component_clause,[],[f74])).
% 4.62/0.97  fof(f679,plain,(
% 4.62/0.97    spl5_8 | spl5_14 | spl5_62 | ~spl5_2),
% 4.62/0.97    inference(avatar_split_clause,[],[f657,f74,f466,f133,f103])).
% 4.62/0.97  fof(f466,plain,(
% 4.62/0.97    spl5_62 <=> ! [X1,X0] : (r1_tsep_1(X0,sK1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK1,X1) | ~m1_pre_topc(sK4,X1) | ~m1_pre_topc(X0,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 4.62/0.97  fof(f657,plain,(
% 4.62/0.97    ( ! [X4,X5] : (r1_tsep_1(X4,sK1) | ~m1_pre_topc(X4,sK4) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_2),
% 4.62/0.97    inference(resolution,[],[f75,f58])).
% 4.62/0.97  fof(f678,plain,(
% 4.62/0.97    spl5_10 | spl5_14 | spl5_86 | ~spl5_80),
% 4.62/0.97    inference(avatar_split_clause,[],[f666,f617,f676,f133,f113])).
% 4.62/0.97  fof(f666,plain,(
% 4.62/0.97    ( ! [X4,X5] : (r1_tsep_1(X4,sK1) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,X5) | v2_struct_0(sK3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_80),
% 4.62/0.97    inference(resolution,[],[f619,f58])).
% 4.62/0.97  fof(f674,plain,(
% 4.62/0.97    spl5_10 | spl5_14 | spl5_85 | ~spl5_80),
% 4.62/0.97    inference(avatar_split_clause,[],[f665,f617,f672,f133,f113])).
% 4.62/0.97  fof(f665,plain,(
% 4.62/0.97    ( ! [X2,X3] : (r1_tsep_1(sK1,X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(sK1,X3) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_80),
% 4.62/0.97    inference(resolution,[],[f619,f59])).
% 4.62/0.97  fof(f670,plain,(
% 4.62/0.97    spl5_14 | spl5_10 | spl5_84 | ~spl5_80),
% 4.62/0.97    inference(avatar_split_clause,[],[f664,f617,f668,f113,f133])).
% 4.62/0.97  fof(f664,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_80),
% 4.62/0.97    inference(resolution,[],[f619,f60])).
% 4.62/0.97  fof(f654,plain,(
% 4.62/0.97    spl5_18 | spl5_83 | ~spl5_60),
% 4.62/0.97    inference(avatar_split_clause,[],[f640,f452,f652,f174])).
% 4.62/0.97  fof(f652,plain,(
% 4.62/0.97    spl5_83 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 4.62/0.97  fof(f452,plain,(
% 4.62/0.97    spl5_60 <=> ! [X3,X2] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | ~m1_pre_topc(sK1,X3) | ~m1_pre_topc(X2,sK1))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 4.62/0.97  fof(f640,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X7) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,sK1) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_60),
% 4.62/0.97    inference(resolution,[],[f453,f167])).
% 4.62/0.97  fof(f453,plain,(
% 4.62/0.97    ( ! [X2,X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2) | ~m1_pre_topc(sK1,X3) | ~m1_pre_topc(X2,sK1)) ) | ~spl5_60),
% 4.62/0.97    inference(avatar_component_clause,[],[f452])).
% 4.62/0.97  fof(f650,plain,(
% 4.62/0.97    spl5_18 | spl5_82 | ~spl5_60),
% 4.62/0.97    inference(avatar_split_clause,[],[f639,f452,f648,f174])).
% 4.62/0.97  fof(f648,plain,(
% 4.62/0.97    spl5_82 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 4.62/0.97  fof(f639,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4) | ~m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_60),
% 4.62/0.97    inference(resolution,[],[f453,f50])).
% 4.62/0.97  fof(f646,plain,(
% 4.62/0.97    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_13 | spl5_81 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_60),
% 4.62/0.97    inference(avatar_split_clause,[],[f642,f452,f148,f143,f138,f644,f128,f98,f103,f118,f123])).
% 4.62/0.97  fof(f642,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_60),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f637])).
% 4.62/0.97  fof(f637,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_60),
% 4.62/0.97    inference(resolution,[],[f453,f68])).
% 4.62/0.97  fof(f620,plain,(
% 4.62/0.97    ~spl5_9 | spl5_80 | spl5_10 | ~spl5_5 | ~spl5_71),
% 4.62/0.97    inference(avatar_split_clause,[],[f606,f546,f88,f113,f617,f108])).
% 4.62/0.97  fof(f546,plain,(
% 4.62/0.97    spl5_71 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK4) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 4.62/0.97  fof(f606,plain,(
% 4.62/0.97    v2_struct_0(sK3) | r1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK3,sK0) | (~spl5_5 | ~spl5_71)),
% 4.62/0.97    inference(resolution,[],[f547,f90])).
% 4.62/0.97  fof(f547,plain,(
% 4.62/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK4) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_71),
% 4.62/0.97    inference(avatar_component_clause,[],[f546])).
% 4.62/0.97  fof(f615,plain,(
% 4.62/0.97    spl5_8 | ~spl5_45 | spl5_79 | ~spl5_71),
% 4.62/0.97    inference(avatar_split_clause,[],[f605,f546,f613,f364,f103])).
% 4.62/0.97  fof(f364,plain,(
% 4.62/0.97    spl5_45 <=> l1_pre_topc(sK4)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 4.62/0.97  fof(f613,plain,(
% 4.62/0.97    spl5_79 <=> ! [X3,X2] : (v2_struct_0(k2_tsep_1(sK4,X2,X3)) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK4) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK4) | ~m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0) | r1_tsep_1(k2_tsep_1(sK4,X2,X3),sK1))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 4.62/0.97  fof(f605,plain,(
% 4.62/0.97    ( ! [X2,X3] : (v2_struct_0(k2_tsep_1(sK4,X2,X3)) | r1_tsep_1(k2_tsep_1(sK4,X2,X3),sK1) | ~m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0) | ~m1_pre_topc(X3,sK4) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK4) | v2_struct_0(X2) | ~l1_pre_topc(sK4) | v2_struct_0(sK4)) ) | ~spl5_71),
% 4.62/0.97    inference(resolution,[],[f547,f68])).
% 4.62/0.97  fof(f611,plain,(
% 4.62/0.97    spl5_8 | ~spl5_45 | spl5_78 | ~spl5_71),
% 4.62/0.97    inference(avatar_split_clause,[],[f604,f546,f609,f364,f103])).
% 4.62/0.97  fof(f609,plain,(
% 4.62/0.97    spl5_78 <=> ! [X1,X0] : (v2_struct_0(k1_tsep_1(sK4,X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK4) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK4) | ~m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0) | r1_tsep_1(k1_tsep_1(sK4,X0,X1),sK1))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 4.62/0.97  fof(f604,plain,(
% 4.62/0.97    ( ! [X0,X1] : (v2_struct_0(k1_tsep_1(sK4,X0,X1)) | r1_tsep_1(k1_tsep_1(sK4,X0,X1),sK1) | ~m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0) | ~m1_pre_topc(X1,sK4) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK4) | v2_struct_0(X0) | ~l1_pre_topc(sK4) | v2_struct_0(sK4)) ) | ~spl5_71),
% 4.62/0.97    inference(resolution,[],[f547,f65])).
% 4.62/0.97  fof(f607,plain,(
% 4.62/0.97    ~spl5_45 | ~spl5_7 | spl5_2 | spl5_8 | ~spl5_71),
% 4.62/0.97    inference(avatar_split_clause,[],[f603,f546,f103,f74,f98,f364])).
% 4.62/0.97  fof(f603,plain,(
% 4.62/0.97    v2_struct_0(sK4) | r1_tsep_1(sK4,sK1) | ~m1_pre_topc(sK4,sK0) | ~l1_pre_topc(sK4) | ~spl5_71),
% 4.62/0.97    inference(resolution,[],[f547,f49])).
% 4.62/0.97  fof(f596,plain,(
% 4.62/0.97    spl5_8 | spl5_14 | spl5_77 | ~spl5_2),
% 4.62/0.97    inference(avatar_split_clause,[],[f591,f74,f594,f133,f103])).
% 4.62/0.97  fof(f591,plain,(
% 4.62/0.97    ( ! [X2,X3] : (r1_tsep_1(sK1,X2) | ~m1_pre_topc(X2,sK4) | ~m1_pre_topc(sK1,X3) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,X3) | v2_struct_0(sK4) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_2),
% 4.62/0.97    inference(resolution,[],[f75,f59])).
% 4.62/0.97  fof(f589,plain,(
% 4.62/0.97    ~spl5_13 | spl5_2 | spl5_14 | ~spl5_6 | ~spl5_68),
% 4.62/0.97    inference(avatar_split_clause,[],[f588,f516,f93,f133,f74,f128])).
% 4.62/0.97  fof(f516,plain,(
% 4.62/0.97    spl5_68 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 4.62/0.97  fof(f588,plain,(
% 4.62/0.97    v2_struct_0(sK1) | r1_tsep_1(sK4,sK1) | ~m1_pre_topc(sK1,sK0) | (~spl5_6 | ~spl5_68)),
% 4.62/0.97    inference(resolution,[],[f517,f95])).
% 4.62/0.97  fof(f95,plain,(
% 4.62/0.97    m1_pre_topc(sK1,sK2) | ~spl5_6),
% 4.62/0.97    inference(avatar_component_clause,[],[f93])).
% 4.62/0.97  fof(f517,plain,(
% 4.62/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_68),
% 4.62/0.97    inference(avatar_component_clause,[],[f516])).
% 4.62/0.97  fof(f574,plain,(
% 4.62/0.97    spl5_18 | spl5_76 | ~spl5_59),
% 4.62/0.97    inference(avatar_split_clause,[],[f560,f448,f572,f174])).
% 4.62/0.97  fof(f572,plain,(
% 4.62/0.97    spl5_76 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X7,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 4.62/0.97  fof(f448,plain,(
% 4.62/0.97    spl5_59 <=> ! [X1,X0] : (r1_tsep_1(X0,sK1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK1,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 4.62/0.97  fof(f560,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,sK1) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_59),
% 4.62/0.97    inference(resolution,[],[f449,f167])).
% 4.62/0.97  fof(f449,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK1,X1) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_59),
% 4.62/0.97    inference(avatar_component_clause,[],[f448])).
% 4.62/0.97  fof(f570,plain,(
% 4.62/0.97    spl5_18 | spl5_75 | ~spl5_59),
% 4.62/0.97    inference(avatar_split_clause,[],[f559,f448,f568,f174])).
% 4.62/0.97  fof(f568,plain,(
% 4.62/0.97    spl5_75 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X4,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 4.62/0.97  fof(f559,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(sK1,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,sK1) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_59),
% 4.62/0.97    inference(resolution,[],[f449,f50])).
% 4.62/0.97  fof(f566,plain,(
% 4.62/0.97    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_13 | spl5_74 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_59),
% 4.62/0.97    inference(avatar_split_clause,[],[f562,f448,f148,f143,f138,f564,f128,f98,f103,f118,f123])).
% 4.62/0.97  fof(f564,plain,(
% 4.62/0.97    spl5_74 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 4.62/0.97  fof(f562,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_59),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f557])).
% 4.62/0.97  fof(f557,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_59),
% 4.62/0.97    inference(resolution,[],[f449,f68])).
% 4.62/0.97  fof(f556,plain,(
% 4.62/0.97    spl5_8 | spl5_73 | ~spl5_62),
% 4.62/0.97    inference(avatar_split_clause,[],[f543,f466,f554,f103])).
% 4.62/0.97  fof(f554,plain,(
% 4.62/0.97    spl5_73 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK4) | r1_tsep_1(X7,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 4.62/0.97  fof(f543,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(sK1,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(X7,sK1) | ~m1_pre_topc(X7,sK4) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_62),
% 4.62/0.97    inference(resolution,[],[f467,f167])).
% 4.62/0.97  fof(f467,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(sK4,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK1,X1) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK4)) ) | ~spl5_62),
% 4.62/0.97    inference(avatar_component_clause,[],[f466])).
% 4.62/0.97  fof(f552,plain,(
% 4.62/0.97    spl5_8 | spl5_72 | ~spl5_62),
% 4.62/0.97    inference(avatar_split_clause,[],[f542,f466,f550,f103])).
% 4.62/0.97  fof(f550,plain,(
% 4.62/0.97    spl5_72 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK4) | r1_tsep_1(X4,sK1) | ~m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 4.62/0.97  fof(f542,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(sK1,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(X4,sK1) | ~m1_pre_topc(X4,sK4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_62),
% 4.62/0.97    inference(resolution,[],[f467,f50])).
% 4.62/0.97  fof(f548,plain,(
% 4.62/0.97    ~spl5_13 | spl5_71 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_7 | ~spl5_62),
% 4.62/0.97    inference(avatar_split_clause,[],[f540,f466,f98,f148,f143,f138,f546,f128])).
% 4.62/0.97  fof(f540,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,sK0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK4)) ) | (~spl5_7 | ~spl5_62)),
% 4.62/0.97    inference(resolution,[],[f467,f100])).
% 4.62/0.97  fof(f526,plain,(
% 4.62/0.97    spl5_8 | spl5_70 | ~spl5_36),
% 4.62/0.97    inference(avatar_split_clause,[],[f513,f279,f524,f103])).
% 4.62/0.97  fof(f524,plain,(
% 4.62/0.97    spl5_70 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(sK4,X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 4.62/0.97  fof(f279,plain,(
% 4.62/0.97    spl5_36 <=> ! [X1,X0] : (r1_tsep_1(sK4,X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK4,X1) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X0,sK2))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 4.62/0.97  fof(f513,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(sK4,X7) | ~m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(X7,sK2) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_36),
% 4.62/0.97    inference(resolution,[],[f280,f167])).
% 4.62/0.97  fof(f280,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(sK4,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X0,sK2)) ) | ~spl5_36),
% 4.62/0.97    inference(avatar_component_clause,[],[f279])).
% 4.62/0.97  fof(f522,plain,(
% 4.62/0.97    spl5_8 | spl5_69 | ~spl5_36),
% 4.62/0.97    inference(avatar_split_clause,[],[f512,f279,f520,f103])).
% 4.62/0.97  fof(f520,plain,(
% 4.62/0.97    spl5_69 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(sK4,X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 4.62/0.97  fof(f512,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(sK4,X4) | ~m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_36),
% 4.62/0.97    inference(resolution,[],[f280,f50])).
% 4.62/0.97  fof(f518,plain,(
% 4.62/0.97    ~spl5_11 | spl5_68 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_7 | ~spl5_36),
% 4.62/0.97    inference(avatar_split_clause,[],[f510,f279,f98,f148,f143,f138,f516,f118])).
% 4.62/0.97  fof(f510,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(sK4,X0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X0,sK2)) ) | (~spl5_7 | ~spl5_36)),
% 4.62/0.97    inference(resolution,[],[f280,f100])).
% 4.62/0.97  fof(f494,plain,(
% 4.62/0.97    spl5_10 | spl5_18 | spl5_67 | ~spl5_50),
% 4.62/0.97    inference(avatar_split_clause,[],[f482,f396,f492,f174,f113])).
% 4.62/0.97  fof(f482,plain,(
% 4.62/0.97    ( ! [X4,X5] : (r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,X5) | v2_struct_0(sK3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_50),
% 4.62/0.97    inference(resolution,[],[f398,f58])).
% 4.62/0.97  fof(f490,plain,(
% 4.62/0.97    spl5_10 | spl5_18 | spl5_66 | ~spl5_50),
% 4.62/0.97    inference(avatar_split_clause,[],[f481,f396,f488,f174,f113])).
% 4.62/0.97  fof(f481,plain,(
% 4.62/0.97    ( ! [X2,X3] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_50),
% 4.62/0.97    inference(resolution,[],[f398,f59])).
% 4.62/0.97  fof(f486,plain,(
% 4.62/0.97    spl5_18 | spl5_10 | spl5_65 | ~spl5_50),
% 4.62/0.97    inference(avatar_split_clause,[],[f480,f396,f484,f113,f174])).
% 4.62/0.97  fof(f480,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_50),
% 4.62/0.97    inference(resolution,[],[f398,f60])).
% 4.62/0.97  fof(f476,plain,(
% 4.62/0.97    spl5_14 | spl5_8 | spl5_64 | ~spl5_58),
% 4.62/0.97    inference(avatar_split_clause,[],[f464,f437,f474,f103,f133])).
% 4.62/0.97  fof(f464,plain,(
% 4.62/0.97    ( ! [X4,X5] : (r1_tsep_1(X4,sK4) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK1) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_58),
% 4.62/0.97    inference(resolution,[],[f439,f58])).
% 4.62/0.97  fof(f472,plain,(
% 4.62/0.97    spl5_14 | spl5_8 | spl5_63 | ~spl5_58),
% 4.62/0.97    inference(avatar_split_clause,[],[f463,f437,f470,f103,f133])).
% 4.62/0.97  fof(f463,plain,(
% 4.62/0.97    ( ! [X2,X3] : (r1_tsep_1(sK4,X2) | ~m1_pre_topc(X2,sK1) | ~m1_pre_topc(sK4,X3) | v2_struct_0(sK4) | ~m1_pre_topc(sK1,X3) | v2_struct_0(sK1) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_58),
% 4.62/0.97    inference(resolution,[],[f439,f59])).
% 4.62/0.97  fof(f468,plain,(
% 4.62/0.97    spl5_8 | spl5_14 | spl5_62 | ~spl5_58),
% 4.62/0.97    inference(avatar_split_clause,[],[f462,f437,f466,f133,f103])).
% 4.62/0.97  fof(f462,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK4) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_58),
% 4.62/0.97    inference(resolution,[],[f439,f60])).
% 4.62/0.97  fof(f458,plain,(
% 4.62/0.97    spl5_14 | spl5_18 | spl5_61 | ~spl5_49),
% 4.62/0.97    inference(avatar_split_clause,[],[f446,f391,f456,f174,f133])).
% 4.62/0.97  fof(f446,plain,(
% 4.62/0.97    ( ! [X4,X5] : (r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,X5) | v2_struct_0(sK1) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_49),
% 4.62/0.97    inference(resolution,[],[f393,f58])).
% 4.62/0.97  fof(f454,plain,(
% 4.62/0.97    spl5_14 | spl5_18 | spl5_60 | ~spl5_49),
% 4.62/0.97    inference(avatar_split_clause,[],[f445,f391,f452,f174,f133])).
% 4.62/0.97  fof(f445,plain,(
% 4.62/0.97    ( ! [X2,X3] : (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2) | ~m1_pre_topc(X2,sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,X3) | v2_struct_0(sK1) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_49),
% 4.62/0.97    inference(resolution,[],[f393,f59])).
% 4.62/0.97  fof(f450,plain,(
% 4.62/0.97    spl5_18 | spl5_14 | spl5_59 | ~spl5_49),
% 4.62/0.97    inference(avatar_split_clause,[],[f444,f391,f448,f133,f174])).
% 4.62/0.97  fof(f444,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_49),
% 4.62/0.97    inference(resolution,[],[f393,f60])).
% 4.62/0.97  fof(f440,plain,(
% 4.62/0.97    ~spl5_13 | spl5_58 | spl5_14 | ~spl5_6 | ~spl5_42),
% 4.62/0.97    inference(avatar_split_clause,[],[f423,f353,f93,f133,f437,f128])).
% 4.62/0.97  fof(f353,plain,(
% 4.62/0.97    spl5_42 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK4) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 4.62/0.97  fof(f423,plain,(
% 4.62/0.97    v2_struct_0(sK1) | r1_tsep_1(sK1,sK4) | ~m1_pre_topc(sK1,sK0) | (~spl5_6 | ~spl5_42)),
% 4.62/0.97    inference(resolution,[],[f354,f95])).
% 4.62/0.97  fof(f354,plain,(
% 4.62/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | r1_tsep_1(X0,sK4) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_42),
% 4.62/0.97    inference(avatar_component_clause,[],[f353])).
% 4.62/0.97  fof(f435,plain,(
% 4.62/0.97    spl5_12 | ~spl5_55 | spl5_57 | ~spl5_42),
% 4.62/0.97    inference(avatar_split_clause,[],[f422,f353,f433,f425,f123])).
% 4.62/0.97  fof(f425,plain,(
% 4.62/0.97    spl5_55 <=> l1_pre_topc(sK2)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 4.62/0.97  fof(f433,plain,(
% 4.62/0.97    spl5_57 <=> ! [X3,X2] : (v2_struct_0(k2_tsep_1(sK2,X2,X3)) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK2) | ~m1_pre_topc(k2_tsep_1(sK2,X2,X3),sK0) | r1_tsep_1(k2_tsep_1(sK2,X2,X3),sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 4.62/0.97  fof(f422,plain,(
% 4.62/0.97    ( ! [X2,X3] : (v2_struct_0(k2_tsep_1(sK2,X2,X3)) | r1_tsep_1(k2_tsep_1(sK2,X2,X3),sK4) | ~m1_pre_topc(k2_tsep_1(sK2,X2,X3),sK0) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl5_42),
% 4.62/0.97    inference(resolution,[],[f354,f68])).
% 4.62/0.97  fof(f431,plain,(
% 4.62/0.97    spl5_12 | ~spl5_55 | spl5_56 | ~spl5_42),
% 4.62/0.97    inference(avatar_split_clause,[],[f421,f353,f429,f425,f123])).
% 4.62/0.97  fof(f429,plain,(
% 4.62/0.97    spl5_56 <=> ! [X1,X0] : (v2_struct_0(k1_tsep_1(sK2,X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0) | r1_tsep_1(k1_tsep_1(sK2,X0,X1),sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 4.62/0.97  fof(f421,plain,(
% 4.62/0.97    ( ! [X0,X1] : (v2_struct_0(k1_tsep_1(sK2,X0,X1)) | r1_tsep_1(k1_tsep_1(sK2,X0,X1),sK4) | ~m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl5_42),
% 4.62/0.97    inference(resolution,[],[f354,f65])).
% 4.62/0.97  fof(f416,plain,(
% 4.62/0.97    spl5_19 | ~spl5_51 | spl5_54 | ~spl5_39),
% 4.62/0.97    inference(avatar_split_clause,[],[f387,f333,f414,f401,f178])).
% 4.62/0.97  fof(f401,plain,(
% 4.62/0.97    spl5_51 <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 4.62/0.97  fof(f414,plain,(
% 4.62/0.97    spl5_54 <=> ! [X3,X2] : (v2_struct_0(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3)) | v2_struct_0(X2) | ~m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X3) | ~m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),sK0) | r1_tsep_1(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),k2_tsep_1(sK0,sK2,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 4.62/0.97  fof(f333,plain,(
% 4.62/0.97    spl5_39 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 4.62/0.97  fof(f387,plain,(
% 4.62/0.97    ( ! [X2,X3] : (v2_struct_0(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3)) | r1_tsep_1(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),sK0) | ~m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X3) | ~m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X2) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))) ) | ~spl5_39),
% 4.62/0.97    inference(resolution,[],[f334,f68])).
% 4.62/0.97  fof(f334,plain,(
% 4.62/0.97    ( ! [X0] : (~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X0) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_39),
% 4.62/0.97    inference(avatar_component_clause,[],[f333])).
% 4.62/0.97  fof(f412,plain,(
% 4.62/0.97    spl5_19 | ~spl5_51 | spl5_53 | ~spl5_39),
% 4.62/0.97    inference(avatar_split_clause,[],[f386,f333,f410,f401,f178])).
% 4.62/0.97  fof(f410,plain,(
% 4.62/0.97    spl5_53 <=> ! [X1,X0] : (v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X1) | ~m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),sK0) | r1_tsep_1(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),k2_tsep_1(sK0,sK2,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 4.62/0.97  fof(f386,plain,(
% 4.62/0.97    ( ! [X0,X1] : (v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1)) | r1_tsep_1(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),sK0) | ~m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X1) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X0) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))) ) | ~spl5_39),
% 4.62/0.97    inference(resolution,[],[f334,f65])).
% 4.62/0.97  fof(f408,plain,(
% 4.62/0.97    ~spl5_51 | ~spl5_22 | spl5_52 | spl5_19 | ~spl5_39),
% 4.62/0.97    inference(avatar_split_clause,[],[f385,f333,f178,f405,f200,f401])).
% 4.62/0.97  fof(f405,plain,(
% 4.62/0.97    spl5_52 <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 4.62/0.97  fof(f385,plain,(
% 4.62/0.97    v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) | ~spl5_39),
% 4.62/0.97    inference(resolution,[],[f334,f49])).
% 4.62/0.97  fof(f399,plain,(
% 4.62/0.97    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_14 | ~spl5_13 | ~spl5_9 | spl5_50 | spl5_10 | ~spl5_39),
% 4.62/0.97    inference(avatar_split_clause,[],[f388,f333,f113,f396,f108,f128,f133,f138,f143,f148])).
% 4.62/0.97  fof(f388,plain,(
% 4.62/0.97    v2_struct_0(sK3) | r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_39),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f384])).
% 4.62/0.97  fof(f384,plain,(
% 4.62/0.97    v2_struct_0(sK3) | r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_39),
% 4.62/0.97    inference(resolution,[],[f334,f167])).
% 4.62/0.97  fof(f394,plain,(
% 4.62/0.97    spl5_17 | ~spl5_16 | ~spl5_15 | spl5_10 | ~spl5_9 | ~spl5_13 | spl5_49 | spl5_14 | ~spl5_39),
% 4.62/0.97    inference(avatar_split_clause,[],[f389,f333,f133,f391,f128,f108,f113,f138,f143,f148])).
% 4.62/0.97  fof(f389,plain,(
% 4.62/0.97    v2_struct_0(sK1) | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_39),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f383])).
% 4.62/0.97  fof(f383,plain,(
% 4.62/0.97    v2_struct_0(sK1) | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_39),
% 4.62/0.97    inference(resolution,[],[f334,f50])).
% 4.62/0.97  fof(f379,plain,(
% 4.62/0.97    spl5_8 | spl5_48 | ~spl5_21),
% 4.62/0.97    inference(avatar_split_clause,[],[f350,f187,f377,f103])).
% 4.62/0.97  fof(f377,plain,(
% 4.62/0.97    spl5_48 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(X7,sK4) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 4.62/0.97  fof(f187,plain,(
% 4.62/0.97    spl5_21 <=> ! [X1,X0] : (r1_tsep_1(X0,sK4) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK4,X1) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X0,sK2))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 4.62/0.97  fof(f350,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,sK4)) | ~v2_pre_topc(k1_tsep_1(X5,X6,sK4)) | ~l1_pre_topc(k1_tsep_1(X5,X6,sK4)) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,sK4)) | r1_tsep_1(X7,sK4) | ~m1_pre_topc(sK2,k1_tsep_1(X5,X6,sK4)) | ~m1_pre_topc(X7,sK2) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(sK4,X5) | v2_struct_0(sK4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_21),
% 4.62/0.97    inference(resolution,[],[f188,f167])).
% 4.62/0.97  fof(f188,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(sK4,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | r1_tsep_1(X0,sK4) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X0,sK2)) ) | ~spl5_21),
% 4.62/0.97    inference(avatar_component_clause,[],[f187])).
% 4.62/0.97  fof(f375,plain,(
% 4.62/0.97    spl5_8 | spl5_47 | ~spl5_21),
% 4.62/0.97    inference(avatar_split_clause,[],[f349,f187,f373,f103])).
% 4.62/0.97  fof(f373,plain,(
% 4.62/0.97    spl5_47 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(X4,sK4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 4.62/0.97  fof(f349,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,sK4,X3)) | ~v2_pre_topc(k1_tsep_1(X2,sK4,X3)) | ~l1_pre_topc(k1_tsep_1(X2,sK4,X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,sK4,X3)) | r1_tsep_1(X4,sK4) | ~m1_pre_topc(sK2,k1_tsep_1(X2,sK4,X3)) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_21),
% 4.62/0.97    inference(resolution,[],[f188,f50])).
% 4.62/0.97  fof(f371,plain,(
% 4.62/0.97    ~spl5_43 | spl5_44 | ~spl5_45 | ~spl5_46 | spl5_8 | ~spl5_21),
% 4.62/0.97    inference(avatar_split_clause,[],[f351,f187,f103,f368,f364,f361,f357])).
% 4.62/0.97  fof(f357,plain,(
% 4.62/0.97    spl5_43 <=> m1_pre_topc(sK2,sK4)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 4.62/0.97  fof(f361,plain,(
% 4.62/0.97    spl5_44 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(X1,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 4.62/0.97  fof(f368,plain,(
% 4.62/0.97    spl5_46 <=> v2_pre_topc(sK4)),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 4.62/0.97  fof(f351,plain,(
% 4.62/0.97    ( ! [X1] : (v2_struct_0(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK4) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK4) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(sK2,sK4) | ~m1_pre_topc(X1,sK2)) ) | ~spl5_21),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f348])).
% 4.62/0.97  fof(f348,plain,(
% 4.62/0.97    ( ! [X1] : (v2_struct_0(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK4) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK4) | r1_tsep_1(X1,sK4) | ~m1_pre_topc(sK2,sK4) | ~m1_pre_topc(X1,sK2) | ~l1_pre_topc(sK4)) ) | ~spl5_21),
% 4.62/0.97    inference(resolution,[],[f188,f49])).
% 4.62/0.97  fof(f355,plain,(
% 4.62/0.97    ~spl5_11 | spl5_42 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_7 | ~spl5_21),
% 4.62/0.97    inference(avatar_split_clause,[],[f347,f187,f98,f148,f143,f138,f353,f118])).
% 4.62/0.97  fof(f347,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X0,sK2)) ) | (~spl5_7 | ~spl5_21)),
% 4.62/0.97    inference(resolution,[],[f188,f100])).
% 4.62/0.97  fof(f343,plain,(
% 4.62/0.97    spl5_18 | spl5_41 | ~spl5_37),
% 4.62/0.97    inference(avatar_split_clause,[],[f329,f301,f341,f174])).
% 4.62/0.97  fof(f341,plain,(
% 4.62/0.97    spl5_41 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 4.62/0.97  fof(f301,plain,(
% 4.62/0.97    spl5_37 <=> ! [X1,X0] : (r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 4.62/0.97  fof(f329,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_37),
% 4.62/0.97    inference(resolution,[],[f302,f167])).
% 4.62/0.97  fof(f302,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))) ) | ~spl5_37),
% 4.62/0.97    inference(avatar_component_clause,[],[f301])).
% 4.62/0.97  fof(f339,plain,(
% 4.62/0.97    spl5_18 | spl5_40 | ~spl5_37),
% 4.62/0.97    inference(avatar_split_clause,[],[f328,f301,f337,f174])).
% 4.62/0.97  fof(f337,plain,(
% 4.62/0.97    spl5_40 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 4.62/0.97  fof(f328,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_37),
% 4.62/0.97    inference(resolution,[],[f302,f50])).
% 4.62/0.97  fof(f335,plain,(
% 4.62/0.97    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_22 | spl5_39 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_37),
% 4.62/0.97    inference(avatar_split_clause,[],[f331,f301,f148,f143,f138,f333,f200,f98,f103,f118,f123])).
% 4.62/0.97  fof(f331,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_37),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f326])).
% 4.62/0.97  fof(f326,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_37),
% 4.62/0.97    inference(resolution,[],[f302,f68])).
% 4.62/0.97  fof(f310,plain,(
% 4.62/0.97    spl5_8 | spl5_12 | spl5_38 | ~spl5_3),
% 4.62/0.97    inference(avatar_split_clause,[],[f304,f79,f308,f123,f103])).
% 4.62/0.97  fof(f304,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK4) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_3),
% 4.62/0.97    inference(resolution,[],[f81,f60])).
% 4.62/0.97  fof(f303,plain,(
% 4.62/0.97    spl5_19 | spl5_18 | spl5_37 | ~spl5_4),
% 4.62/0.97    inference(avatar_split_clause,[],[f299,f83,f301,f174,f178])).
% 4.62/0.97  fof(f299,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_4),
% 4.62/0.97    inference(resolution,[],[f60,f85])).
% 4.62/0.97  fof(f281,plain,(
% 4.62/0.97    spl5_12 | spl5_8 | spl5_36 | ~spl5_3),
% 4.62/0.97    inference(avatar_split_clause,[],[f276,f79,f279,f103,f123])).
% 4.62/0.97  fof(f276,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(sK4,X0) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_3),
% 4.62/0.97    inference(resolution,[],[f81,f59])).
% 4.62/0.97  fof(f275,plain,(
% 4.62/0.97    spl5_18 | spl5_35 | ~spl5_30),
% 4.62/0.97    inference(avatar_split_clause,[],[f261,f235,f273,f174])).
% 4.62/0.97  fof(f273,plain,(
% 4.62/0.97    spl5_35 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X7) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 4.62/0.97  fof(f235,plain,(
% 4.62/0.97    spl5_30 <=> ! [X1,X0] : (r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 4.62/0.97  fof(f261,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X7) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_30),
% 4.62/0.97    inference(resolution,[],[f236,f167])).
% 4.62/0.97  fof(f236,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_30),
% 4.62/0.97    inference(avatar_component_clause,[],[f235])).
% 4.62/0.97  fof(f271,plain,(
% 4.62/0.97    spl5_18 | spl5_34 | ~spl5_30),
% 4.62/0.97    inference(avatar_split_clause,[],[f260,f235,f269,f174])).
% 4.62/0.97  fof(f269,plain,(
% 4.62/0.97    spl5_34 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X4) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 4.62/0.97  fof(f260,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X4) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_30),
% 4.62/0.97    inference(resolution,[],[f236,f50])).
% 4.62/0.97  fof(f267,plain,(
% 4.62/0.97    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_22 | spl5_33 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_30),
% 4.62/0.97    inference(avatar_split_clause,[],[f263,f235,f148,f143,f138,f265,f200,f98,f103,f118,f123])).
% 4.62/0.97  fof(f265,plain,(
% 4.62/0.97    spl5_33 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 4.62/0.97  fof(f263,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_30),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f258])).
% 4.62/0.97  fof(f258,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_30),
% 4.62/0.97    inference(resolution,[],[f236,f68])).
% 4.62/0.97  fof(f251,plain,(
% 4.62/0.97    spl5_18 | ~spl5_26 | spl5_32 | ~spl5_23),
% 4.62/0.97    inference(avatar_split_clause,[],[f243,f204,f249,f215,f174])).
% 4.62/0.97  fof(f215,plain,(
% 4.62/0.97    spl5_26 <=> l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 4.62/0.97  fof(f249,plain,(
% 4.62/0.97    spl5_32 <=> ! [X3,X2] : (v2_struct_0(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3)) | v2_struct_0(X2) | ~m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X3) | ~m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),sK0) | r1_tsep_1(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),k1_tsep_1(sK0,sK1,sK3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 4.62/0.97  fof(f204,plain,(
% 4.62/0.97    spl5_23 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,sK0))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 4.62/0.97  fof(f243,plain,(
% 4.62/0.97    ( ! [X2,X3] : (v2_struct_0(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3)) | r1_tsep_1(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),sK0) | ~m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X3) | ~m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X2) | ~l1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_23),
% 4.62/0.97    inference(resolution,[],[f205,f68])).
% 4.62/0.97  fof(f205,plain,(
% 4.62/0.97    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X0) | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_23),
% 4.62/0.97    inference(avatar_component_clause,[],[f204])).
% 4.62/0.97  fof(f247,plain,(
% 4.62/0.97    spl5_18 | ~spl5_26 | spl5_31 | ~spl5_23),
% 4.62/0.97    inference(avatar_split_clause,[],[f242,f204,f245,f215,f174])).
% 4.62/0.97  fof(f245,plain,(
% 4.62/0.97    spl5_31 <=> ! [X1,X0] : (v2_struct_0(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X1) | ~m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),sK0) | r1_tsep_1(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),k1_tsep_1(sK0,sK1,sK3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 4.62/0.97  fof(f242,plain,(
% 4.62/0.97    ( ! [X0,X1] : (v2_struct_0(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1)) | r1_tsep_1(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),sK0) | ~m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X0) | ~l1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_23),
% 4.62/0.97    inference(resolution,[],[f205,f65])).
% 4.62/0.97  fof(f240,plain,(
% 4.62/0.97    spl5_17 | ~spl5_15 | spl5_14 | ~spl5_13 | spl5_10 | ~spl5_9 | ~spl5_19),
% 4.62/0.97    inference(avatar_split_clause,[],[f239,f178,f108,f113,f128,f133,f138,f148])).
% 4.62/0.97  fof(f239,plain,(
% 4.62/0.97    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_19),
% 4.62/0.97    inference(resolution,[],[f180,f63])).
% 4.62/0.97  fof(f63,plain,(
% 4.62/0.97    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.62/0.97    inference(cnf_transformation,[],[f25])).
% 4.62/0.97  fof(f180,plain,(
% 4.62/0.97    v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~spl5_19),
% 4.62/0.97    inference(avatar_component_clause,[],[f178])).
% 4.62/0.97  fof(f238,plain,(
% 4.62/0.97    spl5_18 | spl5_19 | spl5_20 | ~spl5_4),
% 4.62/0.97    inference(avatar_split_clause,[],[f192,f83,f182,f178,f174])).
% 4.62/0.97  fof(f182,plain,(
% 4.62/0.97    spl5_20 <=> ! [X1,X0] : (r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 4.62/0.97  fof(f192,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_4),
% 4.62/0.97    inference(resolution,[],[f85,f58])).
% 4.62/0.97  fof(f237,plain,(
% 4.62/0.97    spl5_18 | spl5_19 | spl5_30 | ~spl5_4),
% 4.62/0.97    inference(avatar_split_clause,[],[f233,f83,f235,f178,f174])).
% 4.62/0.97  fof(f233,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_4),
% 4.62/0.97    inference(resolution,[],[f59,f85])).
% 4.62/0.97  fof(f232,plain,(
% 4.62/0.97    spl5_17 | ~spl5_15 | spl5_14 | ~spl5_13 | spl5_10 | ~spl5_9 | spl5_22),
% 4.62/0.97    inference(avatar_split_clause,[],[f231,f200,f108,f113,f128,f133,f138,f148])).
% 4.62/0.97  fof(f231,plain,(
% 4.62/0.97    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_22),
% 4.62/0.97    inference(resolution,[],[f202,f65])).
% 4.62/0.97  fof(f202,plain,(
% 4.62/0.97    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | spl5_22),
% 4.62/0.97    inference(avatar_component_clause,[],[f200])).
% 4.62/0.97  fof(f230,plain,(
% 4.62/0.97    spl5_18 | spl5_29 | ~spl5_20),
% 4.62/0.97    inference(avatar_split_clause,[],[f196,f182,f228,f174])).
% 4.62/0.97  fof(f228,plain,(
% 4.62/0.97    spl5_29 <=> ! [X5,X7,X6] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X7,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 4.62/0.97  fof(f196,plain,(
% 4.62/0.97    ( ! [X6,X7,X5] : (v2_struct_0(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~v2_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~l1_pre_topc(k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | v2_struct_0(X7) | ~m1_pre_topc(X7,k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X5,X6,k2_tsep_1(sK0,sK2,sK4))) | r1_tsep_1(X7,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) ) | ~spl5_20),
% 4.62/0.97    inference(resolution,[],[f183,f167])).
% 4.62/0.97  fof(f183,plain,(
% 4.62/0.97    ( ! [X0,X1] : (~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_20),
% 4.62/0.97    inference(avatar_component_clause,[],[f182])).
% 4.62/0.97  fof(f226,plain,(
% 4.62/0.97    spl5_18 | spl5_28 | ~spl5_20),
% 4.62/0.97    inference(avatar_split_clause,[],[f195,f182,f224,f174])).
% 4.62/0.97  fof(f224,plain,(
% 4.62/0.97    spl5_28 <=> ! [X3,X2,X4] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X4,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 4.62/0.97  fof(f195,plain,(
% 4.62/0.97    ( ! [X4,X2,X3] : (v2_struct_0(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~v2_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~l1_pre_topc(k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | v2_struct_0(X4) | ~m1_pre_topc(X4,k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4),X3)) | r1_tsep_1(X4,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_20),
% 4.62/0.97    inference(resolution,[],[f183,f50])).
% 4.62/0.97  fof(f222,plain,(
% 4.62/0.97    ~spl5_24 | spl5_25 | ~spl5_26 | ~spl5_27 | spl5_18 | ~spl5_20),
% 4.62/0.97    inference(avatar_split_clause,[],[f197,f182,f174,f219,f215,f212,f208])).
% 4.62/0.97  fof(f208,plain,(
% 4.62/0.97    spl5_24 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 4.62/0.97  fof(f212,plain,(
% 4.62/0.97    spl5_25 <=> ! [X1] : (v2_struct_0(X1) | r1_tsep_1(X1,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4)))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 4.62/0.97  fof(f219,plain,(
% 4.62/0.97    spl5_27 <=> v2_pre_topc(k2_tsep_1(sK0,sK2,sK4))),
% 4.62/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 4.62/0.97  fof(f197,plain,(
% 4.62/0.97    ( ! [X1] : (v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~v2_pre_topc(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X1) | ~m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X1,k1_tsep_1(sK0,sK1,sK3))) ) | ~spl5_20),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f194])).
% 4.62/0.97  fof(f194,plain,(
% 4.62/0.97    ( ! [X1] : (v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~v2_pre_topc(k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) | v2_struct_0(X1) | ~m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4)) | r1_tsep_1(X1,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4)) | ~l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))) ) | ~spl5_20),
% 4.62/0.97    inference(resolution,[],[f183,f49])).
% 4.62/0.97  fof(f206,plain,(
% 4.62/0.97    spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_22 | spl5_23 | ~spl5_15 | ~spl5_16 | spl5_17 | ~spl5_20),
% 4.62/0.97    inference(avatar_split_clause,[],[f198,f182,f148,f143,f138,f204,f200,f98,f103,f118,f123])).
% 4.62/0.97  fof(f198,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2)) ) | ~spl5_20),
% 4.62/0.97    inference(duplicate_literal_removal,[],[f193])).
% 4.62/0.97  fof(f193,plain,(
% 4.62/0.97    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_20),
% 4.62/0.97    inference(resolution,[],[f183,f68])).
% 4.62/0.97  fof(f191,plain,(
% 4.62/0.97    spl5_17 | ~spl5_15 | spl5_12 | ~spl5_11 | spl5_8 | ~spl5_7 | ~spl5_18),
% 4.62/0.97    inference(avatar_split_clause,[],[f190,f174,f98,f103,f118,f123,f138,f148])).
% 4.62/0.97  fof(f190,plain,(
% 4.62/0.97    ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_18),
% 4.62/0.97    inference(resolution,[],[f176,f66])).
% 4.62/0.97  fof(f66,plain,(
% 4.62/0.97    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.62/0.97    inference(cnf_transformation,[],[f27])).
% 4.62/0.97  fof(f176,plain,(
% 4.62/0.97    v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~spl5_18),
% 4.62/0.97    inference(avatar_component_clause,[],[f174])).
% 4.62/0.97  fof(f189,plain,(
% 4.62/0.97    spl5_12 | spl5_8 | spl5_21 | ~spl5_3),
% 4.62/0.97    inference(avatar_split_clause,[],[f185,f79,f187,f103,f123])).
% 4.62/0.97  fof(f185,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,sK4) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_3),
% 4.62/0.97    inference(resolution,[],[f81,f58])).
% 4.62/0.97  fof(f184,plain,(
% 4.62/0.97    spl5_18 | spl5_19 | spl5_20 | ~spl5_4),
% 4.62/0.97    inference(avatar_split_clause,[],[f172,f83,f182,f178,f174])).
% 4.62/0.97  fof(f172,plain,(
% 4.62/0.97    ( ! [X0,X1] : (r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1) | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_4),
% 4.62/0.97    inference(resolution,[],[f58,f85])).
% 4.62/0.97  fof(f151,plain,(
% 4.62/0.97    ~spl5_17),
% 4.62/0.97    inference(avatar_split_clause,[],[f34,f148])).
% 4.62/0.97  fof(f34,plain,(
% 4.62/0.97    ~v2_struct_0(sK0)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f33,plain,(
% 4.62/0.97    (((((~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 4.62/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f32,f31,f30,f29,f28])).
% 4.62/0.97  fof(f28,plain,(
% 4.62/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 4.62/0.97    introduced(choice_axiom,[])).
% 4.62/0.97  fof(f29,plain,(
% 4.62/0.97    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 4.62/0.97    introduced(choice_axiom,[])).
% 4.62/0.97  fof(f30,plain,(
% 4.62/0.97    ? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(sK2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 4.62/0.97    introduced(choice_axiom,[])).
% 4.62/0.97  fof(f31,plain,(
% 4.62/0.97    ? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(sK2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(sK3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 4.62/0.97    introduced(choice_axiom,[])).
% 4.62/0.97  fof(f32,plain,(
% 4.62/0.97    ? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(sK3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => ((~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 4.62/0.97    introduced(choice_axiom,[])).
% 4.62/0.97  fof(f12,plain,(
% 4.62/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.62/0.97    inference(flattening,[],[f11])).
% 4.62/0.97  fof(f11,plain,(
% 4.62/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4))) & (m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.62/0.97    inference(ennf_transformation,[],[f10])).
% 4.62/0.97  fof(f10,negated_conjecture,(
% 4.62/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 4.62/0.97    inference(negated_conjecture,[],[f9])).
% 4.62/0.97  fof(f9,conjecture,(
% 4.62/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 4.62/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tmap_1)).
% 4.62/0.97  fof(f146,plain,(
% 4.62/0.97    spl5_16),
% 4.62/0.97    inference(avatar_split_clause,[],[f35,f143])).
% 4.62/0.97  fof(f35,plain,(
% 4.62/0.97    v2_pre_topc(sK0)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f141,plain,(
% 4.62/0.97    spl5_15),
% 4.62/0.97    inference(avatar_split_clause,[],[f36,f138])).
% 4.62/0.97  fof(f36,plain,(
% 4.62/0.97    l1_pre_topc(sK0)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f136,plain,(
% 4.62/0.97    ~spl5_14),
% 4.62/0.97    inference(avatar_split_clause,[],[f37,f133])).
% 4.62/0.97  fof(f37,plain,(
% 4.62/0.97    ~v2_struct_0(sK1)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f131,plain,(
% 4.62/0.97    spl5_13),
% 4.62/0.97    inference(avatar_split_clause,[],[f38,f128])).
% 4.62/0.97  fof(f38,plain,(
% 4.62/0.97    m1_pre_topc(sK1,sK0)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f126,plain,(
% 4.62/0.97    ~spl5_12),
% 4.62/0.97    inference(avatar_split_clause,[],[f39,f123])).
% 4.62/0.97  fof(f39,plain,(
% 4.62/0.97    ~v2_struct_0(sK2)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f121,plain,(
% 4.62/0.97    spl5_11),
% 4.62/0.97    inference(avatar_split_clause,[],[f40,f118])).
% 4.62/0.97  fof(f40,plain,(
% 4.62/0.97    m1_pre_topc(sK2,sK0)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f116,plain,(
% 4.62/0.97    ~spl5_10),
% 4.62/0.97    inference(avatar_split_clause,[],[f41,f113])).
% 4.62/0.97  fof(f41,plain,(
% 4.62/0.97    ~v2_struct_0(sK3)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f111,plain,(
% 4.62/0.97    spl5_9),
% 4.62/0.97    inference(avatar_split_clause,[],[f42,f108])).
% 4.62/0.97  fof(f42,plain,(
% 4.62/0.97    m1_pre_topc(sK3,sK0)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f106,plain,(
% 4.62/0.97    ~spl5_8),
% 4.62/0.97    inference(avatar_split_clause,[],[f43,f103])).
% 4.62/0.97  fof(f43,plain,(
% 4.62/0.97    ~v2_struct_0(sK4)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f101,plain,(
% 4.62/0.97    spl5_7),
% 4.62/0.97    inference(avatar_split_clause,[],[f44,f98])).
% 4.62/0.97  fof(f44,plain,(
% 4.62/0.97    m1_pre_topc(sK4,sK0)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f96,plain,(
% 4.62/0.97    spl5_6),
% 4.62/0.97    inference(avatar_split_clause,[],[f45,f93])).
% 4.62/0.97  fof(f45,plain,(
% 4.62/0.97    m1_pre_topc(sK1,sK2)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f91,plain,(
% 4.62/0.97    spl5_5),
% 4.62/0.97    inference(avatar_split_clause,[],[f46,f88])).
% 4.62/0.97  fof(f46,plain,(
% 4.62/0.97    m1_pre_topc(sK3,sK4)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f86,plain,(
% 4.62/0.97    spl5_3 | spl5_4),
% 4.62/0.97    inference(avatar_split_clause,[],[f47,f83,f79])).
% 4.62/0.97  fof(f47,plain,(
% 4.62/0.97    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  fof(f77,plain,(
% 4.62/0.97    ~spl5_1 | ~spl5_2),
% 4.62/0.97    inference(avatar_split_clause,[],[f48,f74,f70])).
% 4.62/0.97  fof(f48,plain,(
% 4.62/0.97    ~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)),
% 4.62/0.97    inference(cnf_transformation,[],[f33])).
% 4.62/0.97  % SZS output end Proof for theBenchmark
% 4.62/0.97  % (4709)------------------------------
% 4.62/0.97  % (4709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/0.97  % (4709)Termination reason: Refutation
% 4.62/0.97  
% 4.62/0.97  % (4709)Memory used [KB]: 7419
% 4.62/0.97  % (4709)Time elapsed: 0.513 s
% 4.62/0.97  % (4709)------------------------------
% 4.62/0.97  % (4709)------------------------------
% 4.62/0.97  % (4704)Success in time 0.603 s
%------------------------------------------------------------------------------
