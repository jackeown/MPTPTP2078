%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t47_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:09 EDT 2019

% Result     : Theorem 1.01s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  755 (2514 expanded)
%              Number of leaves         :  163 (1015 expanded)
%              Depth                    :   20
%              Number of atoms          : 3467 (11168 expanded)
%              Number of equality atoms :  230 ( 617 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1841,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f328,f335,f342,f349,f356,f363,f376,f383,f390,f397,f404,f405,f406,f407,f414,f421,f428,f435,f442,f449,f456,f463,f470,f477,f484,f491,f498,f505,f512,f519,f526,f533,f540,f547,f554,f561,f568,f575,f582,f589,f596,f603,f610,f617,f624,f631,f638,f645,f652,f659,f666,f673,f680,f687,f694,f701,f708,f709,f717,f859,f866,f880,f947,f997,f1007,f1034,f1041,f1048,f1055,f1062,f1069,f1076,f1083,f1090,f1097,f1104,f1111,f1118,f1125,f1132,f1139,f1146,f1153,f1160,f1167,f1174,f1181,f1188,f1195,f1202,f1208,f1212,f1239,f1246,f1253,f1260,f1267,f1274,f1281,f1288,f1295,f1302,f1309,f1316,f1323,f1429,f1456,f1460,f1536,f1544,f1551,f1560,f1567,f1574,f1581,f1588,f1595,f1602,f1611,f1626,f1634,f1642,f1650,f1658,f1666,f1673,f1680,f1685,f1692,f1699,f1706,f1714,f1721,f1728,f1737,f1744,f1751,f1758,f1765,f1772,f1779,f1784,f1791,f1798,f1808,f1828,f1830,f1831,f1832,f1840])).

fof(f1840,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f1839])).

fof(f1839,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f1838,f348])).

fof(f348,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl10_7
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f1838,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f1837,f341])).

fof(f341,plain,
    ( l3_lattices(sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl10_4
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f1837,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f1836,f334])).

fof(f334,plain,
    ( v10_lattices(sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl10_2
  <=> v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1836,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f1835,f327])).

fof(f327,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1835,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f1834,f362])).

fof(f362,plain,
    ( l3_lattices(sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl10_10
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1834,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_8
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f1833,f355])).

fof(f355,plain,
    ( v10_lattices(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl10_8
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f1833,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_17 ),
    inference(resolution,[],[f379,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ( v10_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ( v10_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f84])).

fof(f84,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v10_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',fc3_filter_1)).

fof(f379,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl10_17
  <=> ~ v10_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f1832,plain,
    ( spl10_22
    | ~ spl10_221
    | spl10_7
    | ~ spl10_10
    | ~ spl10_212
    | ~ spl10_218 ),
    inference(avatar_split_clause,[],[f1814,f1525,f1507,f361,f347,f1534,f402])).

fof(f402,plain,
    ( spl10_22
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f1534,plain,
    ( spl10_221
  <=> ~ v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_221])])).

fof(f1507,plain,
    ( spl10_212
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_212])])).

fof(f1525,plain,
    ( spl10_218
  <=> v16_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_218])])).

fof(f1814,plain,
    ( ~ v15_lattices(sK0)
    | v17_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_212
    | ~ spl10_218 ),
    inference(subsumption_resolution,[],[f1813,f362])).

fof(f1813,plain,
    ( ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v17_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_212
    | ~ spl10_218 ),
    inference(subsumption_resolution,[],[f1812,f1508])).

fof(f1508,plain,
    ( v11_lattices(sK0)
    | ~ spl10_212 ),
    inference(avatar_component_clause,[],[f1507])).

fof(f1812,plain,
    ( ~ v11_lattices(sK0)
    | ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v17_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_218 ),
    inference(subsumption_resolution,[],[f1799,f348])).

fof(f1799,plain,
    ( v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v17_lattices(sK0)
    | ~ spl10_218 ),
    inference(resolution,[],[f1526,f247])).

fof(f247,plain,(
    ! [X0] :
      ( ~ v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ v11_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0)
      | v17_lattices(X0) ) ),
    inference(cnf_transformation,[],[f153])).

fof(f153,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f152])).

fof(f152,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v17_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',cc6_lattices)).

fof(f1526,plain,
    ( v16_lattices(sK0)
    | ~ spl10_218 ),
    inference(avatar_component_clause,[],[f1525])).

fof(f1831,plain,
    ( spl10_12
    | ~ spl10_211
    | spl10_1
    | ~ spl10_4
    | ~ spl10_214
    | ~ spl10_216 ),
    inference(avatar_split_clause,[],[f1811,f1519,f1513,f340,f326,f1504,f368])).

fof(f368,plain,
    ( spl10_12
  <=> v17_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f1504,plain,
    ( spl10_211
  <=> ~ v11_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_211])])).

fof(f1513,plain,
    ( spl10_214
  <=> v16_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_214])])).

fof(f1519,plain,
    ( spl10_216
  <=> v15_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_216])])).

fof(f1811,plain,
    ( ~ v11_lattices(sK1)
    | v17_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_214
    | ~ spl10_216 ),
    inference(subsumption_resolution,[],[f1810,f341])).

fof(f1810,plain,
    ( ~ v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v17_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_214
    | ~ spl10_216 ),
    inference(subsumption_resolution,[],[f1809,f1520])).

fof(f1520,plain,
    ( v15_lattices(sK1)
    | ~ spl10_216 ),
    inference(avatar_component_clause,[],[f1519])).

fof(f1809,plain,
    ( ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v17_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_214 ),
    inference(subsumption_resolution,[],[f1707,f327])).

fof(f1707,plain,
    ( v2_struct_0(sK1)
    | ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v17_lattices(sK1)
    | ~ spl10_214 ),
    inference(resolution,[],[f1514,f247])).

fof(f1514,plain,
    ( v16_lattices(sK1)
    | ~ spl10_214 ),
    inference(avatar_component_clause,[],[f1513])).

fof(f1830,plain,
    ( spl10_210
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f1829,f388,f361,f354,f347,f340,f333,f326,f1501])).

fof(f1501,plain,
    ( spl10_210
  <=> v11_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_210])])).

fof(f388,plain,
    ( spl10_18
  <=> v17_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f1829,plain,
    ( v11_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1825,f355])).

fof(f1825,plain,
    ( v11_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1824,f348])).

fof(f1824,plain,
    ( v2_struct_0(sK0)
    | v11_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1823,f341])).

fof(f1823,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1822,f334])).

fof(f1822,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1821,f327])).

fof(f1821,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1819,f362])).

fof(f1819,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_18 ),
    inference(resolution,[],[f389,f738])).

fof(f738,plain,(
    ! [X2,X3] :
      ( ~ v17_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(X2)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X2)
      | v11_lattices(X3)
      | ~ v10_lattices(X2) ) ),
    inference(subsumption_resolution,[],[f737,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f62])).

fof(f62,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',dt_k7_filter_1)).

fof(f737,plain,(
    ! [X2,X3] :
      ( ~ v10_lattices(X2)
      | ~ l3_lattices(X2)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X2)
      | v11_lattices(X3)
      | ~ v17_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f733,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',fc2_filter_1)).

fof(f733,plain,(
    ! [X2,X3] :
      ( ~ v10_lattices(X2)
      | ~ l3_lattices(X2)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X2)
      | v11_lattices(X3)
      | v2_struct_0(k7_filter_1(X2,X3))
      | ~ v17_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3)) ) ),
    inference(resolution,[],[f321,f248])).

fof(f248,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f154])).

fof(f154,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',cc5_lattices)).

fof(f321,plain,(
    ! [X0,X1] :
      ( ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v11_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f320,f216])).

fof(f320,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f319,f214])).

fof(f319,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f228,f217])).

fof(f228,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X1) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f146])).

fof(f146,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f128])).

fof(f128,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',t39_filter_1)).

fof(f389,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f388])).

fof(f1828,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | spl10_211 ),
    inference(avatar_contradiction_clause,[],[f1827])).

fof(f1827,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_211 ),
    inference(subsumption_resolution,[],[f1826,f355])).

fof(f1826,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_211 ),
    inference(subsumption_resolution,[],[f1825,f1505])).

fof(f1505,plain,
    ( ~ v11_lattices(sK1)
    | ~ spl10_211 ),
    inference(avatar_component_clause,[],[f1504])).

fof(f1808,plain,
    ( spl10_7
    | ~ spl10_10
    | ~ spl10_22
    | spl10_221 ),
    inference(avatar_contradiction_clause,[],[f1807])).

fof(f1807,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_221 ),
    inference(subsumption_resolution,[],[f1806,f362])).

fof(f1806,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_22
    | ~ spl10_221 ),
    inference(subsumption_resolution,[],[f1805,f403])).

fof(f403,plain,
    ( v17_lattices(sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f402])).

fof(f1805,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_221 ),
    inference(subsumption_resolution,[],[f1801,f348])).

fof(f1801,plain,
    ( v2_struct_0(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_221 ),
    inference(resolution,[],[f1535,f249])).

fof(f249,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f155])).

fof(f1535,plain,
    ( ~ v15_lattices(sK0)
    | ~ spl10_221 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f1798,plain,
    ( spl10_270
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f987,f643,f636,f1796])).

fof(f1796,plain,
    ( spl10_270
  <=> k7_filter_1(sK8,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK8),u2_lattices(sK8),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK8),u1_lattices(sK8),u1_lattices(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_270])])).

fof(f636,plain,
    ( spl10_88
  <=> l3_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f643,plain,
    ( spl10_91
  <=> ~ v2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f987,plain,
    ( k7_filter_1(sK8,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK8),u2_lattices(sK8),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK8),u1_lattices(sK8),u1_lattices(sK8)))
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f978,f644])).

fof(f644,plain,
    ( ~ v2_struct_0(sK8)
    | ~ spl10_91 ),
    inference(avatar_component_clause,[],[f643])).

fof(f978,plain,
    ( v2_struct_0(sK8)
    | k7_filter_1(sK8,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK8),u2_lattices(sK8),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK8),u1_lattices(sK8),u1_lattices(sK8)))
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(resolution,[],[f791,f637])).

fof(f637,plain,
    ( l3_lattices(sK8)
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f636])).

fof(f791,plain,
    ( ! [X12] :
        ( ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | k7_filter_1(X12,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(X12),u1_struct_0(sK8),u2_lattices(X12),u2_lattices(sK8)),k6_filter_1(u1_struct_0(X12),u1_struct_0(sK8),u1_lattices(X12),u1_lattices(sK8))) )
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f782,f644])).

fof(f782,plain,
    ( ! [X12] :
        ( ~ l3_lattices(X12)
        | v2_struct_0(sK8)
        | v2_struct_0(X12)
        | k7_filter_1(X12,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(X12),u1_struct_0(sK8),u2_lattices(X12),u2_lattices(sK8)),k6_filter_1(u1_struct_0(X12),u1_struct_0(sK8),u1_lattices(X12),u1_lattices(sK8))) )
    | ~ spl10_88 ),
    inference(resolution,[],[f234,f637])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1))) ) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1)))
          | ~ l3_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f148])).

fof(f148,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1)))
          | ~ l3_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & ~ v2_struct_0(X1) )
         => k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',d7_filter_1)).

fof(f1791,plain,
    ( spl10_268
    | ~ spl10_66
    | spl10_69
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f986,f643,f636,f566,f559,f1789])).

fof(f1789,plain,
    ( spl10_268
  <=> k7_filter_1(sK7,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK8),u2_lattices(sK7),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK8),u1_lattices(sK7),u1_lattices(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_268])])).

fof(f559,plain,
    ( spl10_66
  <=> l3_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f566,plain,
    ( spl10_69
  <=> ~ v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f986,plain,
    ( k7_filter_1(sK7,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK8),u2_lattices(sK7),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK8),u1_lattices(sK7),u1_lattices(sK8)))
    | ~ spl10_66
    | ~ spl10_69
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f977,f567])).

fof(f567,plain,
    ( ~ v2_struct_0(sK7)
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f566])).

fof(f977,plain,
    ( v2_struct_0(sK7)
    | k7_filter_1(sK7,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK8),u2_lattices(sK7),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK8),u1_lattices(sK7),u1_lattices(sK8)))
    | ~ spl10_66
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(resolution,[],[f791,f560])).

fof(f560,plain,
    ( l3_lattices(sK7)
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f559])).

fof(f1784,plain,
    ( spl10_7
    | ~ spl10_10
    | ~ spl10_22
    | spl10_219 ),
    inference(avatar_contradiction_clause,[],[f1783])).

fof(f1783,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_219 ),
    inference(subsumption_resolution,[],[f1782,f362])).

fof(f1782,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_22
    | ~ spl10_219 ),
    inference(subsumption_resolution,[],[f1781,f403])).

fof(f1781,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_219 ),
    inference(subsumption_resolution,[],[f1780,f348])).

fof(f1780,plain,
    ( v2_struct_0(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_219 ),
    inference(resolution,[],[f1529,f250])).

fof(f250,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f155])).

fof(f1529,plain,
    ( ~ v16_lattices(sK0)
    | ~ spl10_219 ),
    inference(avatar_component_clause,[],[f1528])).

fof(f1528,plain,
    ( spl10_219
  <=> ~ v16_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_219])])).

fof(f1779,plain,
    ( spl10_266
    | ~ spl10_58
    | spl10_61
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f985,f643,f636,f538,f531,f1777])).

fof(f1777,plain,
    ( spl10_266
  <=> k7_filter_1(sK5,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK8),u2_lattices(sK5),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK8),u1_lattices(sK5),u1_lattices(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_266])])).

fof(f531,plain,
    ( spl10_58
  <=> l3_lattices(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f538,plain,
    ( spl10_61
  <=> ~ v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f985,plain,
    ( k7_filter_1(sK5,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK8),u2_lattices(sK5),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK8),u1_lattices(sK5),u1_lattices(sK8)))
    | ~ spl10_58
    | ~ spl10_61
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f975,f539])).

fof(f539,plain,
    ( ~ v2_struct_0(sK5)
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f538])).

fof(f975,plain,
    ( v2_struct_0(sK5)
    | k7_filter_1(sK5,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK8),u2_lattices(sK5),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK8),u1_lattices(sK5),u1_lattices(sK8)))
    | ~ spl10_58
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(resolution,[],[f791,f532])).

fof(f532,plain,
    ( l3_lattices(sK5)
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f531])).

fof(f1772,plain,
    ( spl10_264
    | ~ spl10_50
    | spl10_53
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f984,f643,f636,f510,f503,f1770])).

fof(f1770,plain,
    ( spl10_264
  <=> k7_filter_1(sK4,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK8),u2_lattices(sK4),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK8),u1_lattices(sK4),u1_lattices(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_264])])).

fof(f503,plain,
    ( spl10_50
  <=> l3_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f510,plain,
    ( spl10_53
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f984,plain,
    ( k7_filter_1(sK4,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK8),u2_lattices(sK4),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK8),u1_lattices(sK4),u1_lattices(sK8)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f974,f511])).

fof(f511,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f510])).

fof(f974,plain,
    ( v2_struct_0(sK4)
    | k7_filter_1(sK4,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK8),u2_lattices(sK4),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK8),u1_lattices(sK4),u1_lattices(sK8)))
    | ~ spl10_50
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(resolution,[],[f791,f504])).

fof(f504,plain,
    ( l3_lattices(sK4)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f503])).

fof(f1765,plain,
    ( spl10_262
    | ~ spl10_24
    | spl10_27
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f983,f643,f636,f419,f412,f1763])).

fof(f1763,plain,
    ( spl10_262
  <=> k7_filter_1(sK2,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK8),u2_lattices(sK2),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK8),u1_lattices(sK2),u1_lattices(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_262])])).

fof(f412,plain,
    ( spl10_24
  <=> l3_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f419,plain,
    ( spl10_27
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f983,plain,
    ( k7_filter_1(sK2,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK8),u2_lattices(sK2),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK8),u1_lattices(sK2),u1_lattices(sK8)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f972,f420])).

fof(f420,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f419])).

fof(f972,plain,
    ( v2_struct_0(sK2)
    | k7_filter_1(sK2,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK8),u2_lattices(sK2),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK8),u1_lattices(sK2),u1_lattices(sK8)))
    | ~ spl10_24
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(resolution,[],[f791,f413])).

fof(f413,plain,
    ( l3_lattices(sK2)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f412])).

fof(f1758,plain,
    ( spl10_260
    | ~ spl10_66
    | spl10_69
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f967,f643,f636,f566,f559,f1756])).

fof(f1756,plain,
    ( spl10_260
  <=> k7_filter_1(sK8,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK7),u2_lattices(sK8),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_lattices(sK8),u1_lattices(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_260])])).

fof(f967,plain,
    ( k7_filter_1(sK8,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK7),u2_lattices(sK8),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_lattices(sK8),u1_lattices(sK7)))
    | ~ spl10_66
    | ~ spl10_69
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f958,f644])).

fof(f958,plain,
    ( v2_struct_0(sK8)
    | k7_filter_1(sK8,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK7),u2_lattices(sK8),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_lattices(sK8),u1_lattices(sK7)))
    | ~ spl10_66
    | ~ spl10_69
    | ~ spl10_88 ),
    inference(resolution,[],[f790,f637])).

fof(f790,plain,
    ( ! [X11] :
        ( ~ l3_lattices(X11)
        | v2_struct_0(X11)
        | k7_filter_1(X11,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(X11),u1_struct_0(sK7),u2_lattices(X11),u2_lattices(sK7)),k6_filter_1(u1_struct_0(X11),u1_struct_0(sK7),u1_lattices(X11),u1_lattices(sK7))) )
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f781,f567])).

fof(f781,plain,
    ( ! [X11] :
        ( ~ l3_lattices(X11)
        | v2_struct_0(sK7)
        | v2_struct_0(X11)
        | k7_filter_1(X11,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(X11),u1_struct_0(sK7),u2_lattices(X11),u2_lattices(sK7)),k6_filter_1(u1_struct_0(X11),u1_struct_0(sK7),u1_lattices(X11),u1_lattices(sK7))) )
    | ~ spl10_66 ),
    inference(resolution,[],[f234,f560])).

fof(f1751,plain,
    ( spl10_258
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f966,f566,f559,f1749])).

fof(f1749,plain,
    ( spl10_258
  <=> k7_filter_1(sK7,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK7),u2_lattices(sK7),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK7),u1_lattices(sK7),u1_lattices(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_258])])).

fof(f966,plain,
    ( k7_filter_1(sK7,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK7),u2_lattices(sK7),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK7),u1_lattices(sK7),u1_lattices(sK7)))
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f957,f567])).

fof(f957,plain,
    ( v2_struct_0(sK7)
    | k7_filter_1(sK7,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK7),u2_lattices(sK7),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK7),u1_lattices(sK7),u1_lattices(sK7)))
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(resolution,[],[f790,f560])).

fof(f1744,plain,
    ( spl10_256
    | ~ spl10_58
    | spl10_61
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f965,f566,f559,f538,f531,f1742])).

fof(f1742,plain,
    ( spl10_256
  <=> k7_filter_1(sK5,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK7),u2_lattices(sK5),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK7),u1_lattices(sK5),u1_lattices(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_256])])).

fof(f965,plain,
    ( k7_filter_1(sK5,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK7),u2_lattices(sK5),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK7),u1_lattices(sK5),u1_lattices(sK7)))
    | ~ spl10_58
    | ~ spl10_61
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f955,f539])).

fof(f955,plain,
    ( v2_struct_0(sK5)
    | k7_filter_1(sK5,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK7),u2_lattices(sK5),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK7),u1_lattices(sK5),u1_lattices(sK7)))
    | ~ spl10_58
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(resolution,[],[f790,f532])).

fof(f1737,plain,
    ( spl10_1
    | ~ spl10_4
    | ~ spl10_12
    | spl10_217 ),
    inference(avatar_contradiction_clause,[],[f1736])).

fof(f1736,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_217 ),
    inference(subsumption_resolution,[],[f1735,f341])).

fof(f1735,plain,
    ( ~ l3_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_217 ),
    inference(subsumption_resolution,[],[f1734,f369])).

fof(f369,plain,
    ( v17_lattices(sK1)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f368])).

fof(f1734,plain,
    ( ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_217 ),
    inference(subsumption_resolution,[],[f1730,f327])).

fof(f1730,plain,
    ( v2_struct_0(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl10_217 ),
    inference(resolution,[],[f1523,f249])).

fof(f1523,plain,
    ( ~ v15_lattices(sK1)
    | ~ spl10_217 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1522,plain,
    ( spl10_217
  <=> ~ v15_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_217])])).

fof(f1728,plain,
    ( spl10_254
    | ~ spl10_50
    | spl10_53
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f964,f566,f559,f510,f503,f1726])).

fof(f1726,plain,
    ( spl10_254
  <=> k7_filter_1(sK4,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK7),u2_lattices(sK4),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK7),u1_lattices(sK4),u1_lattices(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_254])])).

fof(f964,plain,
    ( k7_filter_1(sK4,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK7),u2_lattices(sK4),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK7),u1_lattices(sK4),u1_lattices(sK7)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f954,f511])).

fof(f954,plain,
    ( v2_struct_0(sK4)
    | k7_filter_1(sK4,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK7),u2_lattices(sK4),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK7),u1_lattices(sK4),u1_lattices(sK7)))
    | ~ spl10_50
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(resolution,[],[f790,f504])).

fof(f1721,plain,
    ( spl10_252
    | ~ spl10_24
    | spl10_27
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f963,f566,f559,f419,f412,f1719])).

fof(f1719,plain,
    ( spl10_252
  <=> k7_filter_1(sK2,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK7),u2_lattices(sK2),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK7),u1_lattices(sK2),u1_lattices(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_252])])).

fof(f963,plain,
    ( k7_filter_1(sK2,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK7),u2_lattices(sK2),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK7),u1_lattices(sK2),u1_lattices(sK7)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f952,f420])).

fof(f952,plain,
    ( v2_struct_0(sK2)
    | k7_filter_1(sK2,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK7),u2_lattices(sK2),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK7),u1_lattices(sK2),u1_lattices(sK7)))
    | ~ spl10_24
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(resolution,[],[f790,f413])).

fof(f1714,plain,
    ( spl10_250
    | ~ spl10_58
    | spl10_61
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f940,f643,f636,f538,f531,f1712])).

fof(f1712,plain,
    ( spl10_250
  <=> k7_filter_1(sK8,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK5),u2_lattices(sK8),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK5),u1_lattices(sK8),u1_lattices(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_250])])).

fof(f940,plain,
    ( k7_filter_1(sK8,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK5),u2_lattices(sK8),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK5),u1_lattices(sK8),u1_lattices(sK5)))
    | ~ spl10_58
    | ~ spl10_61
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f931,f644])).

fof(f931,plain,
    ( v2_struct_0(sK8)
    | k7_filter_1(sK8,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK5),u2_lattices(sK8),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK5),u1_lattices(sK8),u1_lattices(sK5)))
    | ~ spl10_58
    | ~ spl10_61
    | ~ spl10_88 ),
    inference(resolution,[],[f789,f637])).

fof(f789,plain,
    ( ! [X9] :
        ( ~ l3_lattices(X9)
        | v2_struct_0(X9)
        | k7_filter_1(X9,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(X9),u1_struct_0(sK5),u2_lattices(X9),u2_lattices(sK5)),k6_filter_1(u1_struct_0(X9),u1_struct_0(sK5),u1_lattices(X9),u1_lattices(sK5))) )
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f779,f539])).

fof(f779,plain,
    ( ! [X9] :
        ( ~ l3_lattices(X9)
        | v2_struct_0(sK5)
        | v2_struct_0(X9)
        | k7_filter_1(X9,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(X9),u1_struct_0(sK5),u2_lattices(X9),u2_lattices(sK5)),k6_filter_1(u1_struct_0(X9),u1_struct_0(sK5),u1_lattices(X9),u1_lattices(sK5))) )
    | ~ spl10_58 ),
    inference(resolution,[],[f234,f532])).

fof(f1706,plain,
    ( spl10_248
    | ~ spl10_58
    | spl10_61
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f939,f566,f559,f538,f531,f1704])).

fof(f1704,plain,
    ( spl10_248
  <=> k7_filter_1(sK7,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK5),u2_lattices(sK7),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_lattices(sK7),u1_lattices(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_248])])).

fof(f939,plain,
    ( k7_filter_1(sK7,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK5),u2_lattices(sK7),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_lattices(sK7),u1_lattices(sK5)))
    | ~ spl10_58
    | ~ spl10_61
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f930,f567])).

fof(f930,plain,
    ( v2_struct_0(sK7)
    | k7_filter_1(sK7,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK5),u2_lattices(sK7),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_lattices(sK7),u1_lattices(sK5)))
    | ~ spl10_58
    | ~ spl10_61
    | ~ spl10_66 ),
    inference(resolution,[],[f789,f560])).

fof(f1699,plain,
    ( spl10_246
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f938,f538,f531,f1697])).

fof(f1697,plain,
    ( spl10_246
  <=> k7_filter_1(sK5,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK5),u2_lattices(sK5),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK5),u1_lattices(sK5),u1_lattices(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_246])])).

fof(f938,plain,
    ( k7_filter_1(sK5,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK5),u2_lattices(sK5),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK5),u1_lattices(sK5),u1_lattices(sK5)))
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f928,f539])).

fof(f928,plain,
    ( v2_struct_0(sK5)
    | k7_filter_1(sK5,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK5),u2_lattices(sK5),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK5),u1_lattices(sK5),u1_lattices(sK5)))
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(resolution,[],[f789,f532])).

fof(f1692,plain,
    ( spl10_244
    | ~ spl10_50
    | spl10_53
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f937,f538,f531,f510,f503,f1690])).

fof(f1690,plain,
    ( spl10_244
  <=> k7_filter_1(sK4,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK5),u2_lattices(sK4),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK5),u1_lattices(sK4),u1_lattices(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_244])])).

fof(f937,plain,
    ( k7_filter_1(sK4,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK5),u2_lattices(sK4),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK5),u1_lattices(sK4),u1_lattices(sK5)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f927,f511])).

fof(f927,plain,
    ( v2_struct_0(sK4)
    | k7_filter_1(sK4,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK5),u2_lattices(sK4),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK5),u1_lattices(sK4),u1_lattices(sK5)))
    | ~ spl10_50
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(resolution,[],[f789,f504])).

fof(f1685,plain,
    ( spl10_1
    | ~ spl10_4
    | ~ spl10_12
    | spl10_215 ),
    inference(avatar_contradiction_clause,[],[f1684])).

fof(f1684,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_215 ),
    inference(subsumption_resolution,[],[f1683,f341])).

fof(f1683,plain,
    ( ~ l3_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_215 ),
    inference(subsumption_resolution,[],[f1682,f369])).

fof(f1682,plain,
    ( ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_215 ),
    inference(subsumption_resolution,[],[f1681,f327])).

fof(f1681,plain,
    ( v2_struct_0(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl10_215 ),
    inference(resolution,[],[f1517,f250])).

fof(f1517,plain,
    ( ~ v16_lattices(sK1)
    | ~ spl10_215 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f1516,plain,
    ( spl10_215
  <=> ~ v16_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_215])])).

fof(f1680,plain,
    ( spl10_242
    | ~ spl10_24
    | spl10_27
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f936,f538,f531,f419,f412,f1678])).

fof(f1678,plain,
    ( spl10_242
  <=> k7_filter_1(sK2,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK5),u2_lattices(sK2),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK5),u1_lattices(sK2),u1_lattices(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_242])])).

fof(f936,plain,
    ( k7_filter_1(sK2,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK5),u2_lattices(sK2),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK5),u1_lattices(sK2),u1_lattices(sK5)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f925,f420])).

fof(f925,plain,
    ( v2_struct_0(sK2)
    | k7_filter_1(sK2,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK5),u2_lattices(sK2),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK5),u1_lattices(sK2),u1_lattices(sK5)))
    | ~ spl10_24
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(resolution,[],[f789,f413])).

fof(f1673,plain,
    ( spl10_240
    | ~ spl10_50
    | spl10_53
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f920,f643,f636,f510,f503,f1671])).

fof(f1671,plain,
    ( spl10_240
  <=> k7_filter_1(sK8,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK4),u2_lattices(sK8),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK4),u1_lattices(sK8),u1_lattices(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_240])])).

fof(f920,plain,
    ( k7_filter_1(sK8,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK4),u2_lattices(sK8),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK4),u1_lattices(sK8),u1_lattices(sK4)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f911,f644])).

fof(f911,plain,
    ( v2_struct_0(sK8)
    | k7_filter_1(sK8,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK4),u2_lattices(sK8),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK4),u1_lattices(sK8),u1_lattices(sK4)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_88 ),
    inference(resolution,[],[f788,f637])).

fof(f788,plain,
    ( ! [X8] :
        ( ~ l3_lattices(X8)
        | v2_struct_0(X8)
        | k7_filter_1(X8,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(X8),u1_struct_0(sK4),u2_lattices(X8),u2_lattices(sK4)),k6_filter_1(u1_struct_0(X8),u1_struct_0(sK4),u1_lattices(X8),u1_lattices(sK4))) )
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f778,f511])).

fof(f778,plain,
    ( ! [X8] :
        ( ~ l3_lattices(X8)
        | v2_struct_0(sK4)
        | v2_struct_0(X8)
        | k7_filter_1(X8,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(X8),u1_struct_0(sK4),u2_lattices(X8),u2_lattices(sK4)),k6_filter_1(u1_struct_0(X8),u1_struct_0(sK4),u1_lattices(X8),u1_lattices(sK4))) )
    | ~ spl10_50 ),
    inference(resolution,[],[f234,f504])).

fof(f1666,plain,
    ( spl10_238
    | ~ spl10_50
    | spl10_53
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f919,f566,f559,f510,f503,f1664])).

fof(f1664,plain,
    ( spl10_238
  <=> k7_filter_1(sK7,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK4),u2_lattices(sK7),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK4),u1_lattices(sK7),u1_lattices(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_238])])).

fof(f919,plain,
    ( k7_filter_1(sK7,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK4),u2_lattices(sK7),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK4),u1_lattices(sK7),u1_lattices(sK4)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f910,f567])).

fof(f910,plain,
    ( v2_struct_0(sK7)
    | k7_filter_1(sK7,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK4),u2_lattices(sK7),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK4),u1_lattices(sK7),u1_lattices(sK4)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_66 ),
    inference(resolution,[],[f788,f560])).

fof(f1658,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | spl10_213 ),
    inference(avatar_contradiction_clause,[],[f1657])).

fof(f1657,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_213 ),
    inference(subsumption_resolution,[],[f1656,f355])).

fof(f1656,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_213 ),
    inference(subsumption_resolution,[],[f1655,f1511])).

fof(f1511,plain,
    ( ~ v11_lattices(sK0)
    | ~ spl10_213 ),
    inference(avatar_component_clause,[],[f1510])).

fof(f1510,plain,
    ( spl10_213
  <=> ~ v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_213])])).

fof(f1655,plain,
    ( v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1654,f348])).

fof(f1654,plain,
    ( v2_struct_0(sK0)
    | v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1653,f341])).

fof(f1653,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1652,f334])).

fof(f1652,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1651,f327])).

fof(f1651,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1618,f362])).

fof(f1618,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_18 ),
    inference(resolution,[],[f389,f731])).

fof(f731,plain,(
    ! [X2,X3] :
      ( ~ v17_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(X2)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X2)
      | v11_lattices(X2)
      | ~ v10_lattices(X2) ) ),
    inference(subsumption_resolution,[],[f730,f216])).

fof(f730,plain,(
    ! [X2,X3] :
      ( ~ v10_lattices(X2)
      | ~ l3_lattices(X2)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X2)
      | v11_lattices(X2)
      | ~ v17_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f726,f217])).

fof(f726,plain,(
    ! [X2,X3] :
      ( ~ v10_lattices(X2)
      | ~ l3_lattices(X2)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X2)
      | v11_lattices(X2)
      | v2_struct_0(k7_filter_1(X2,X3))
      | ~ v17_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3)) ) ),
    inference(resolution,[],[f318,f248])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v11_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f317,f216])).

fof(f317,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f316,f214])).

fof(f316,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f229,f217])).

fof(f229,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f1650,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | spl10_221 ),
    inference(avatar_contradiction_clause,[],[f1649])).

fof(f1649,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_221 ),
    inference(subsumption_resolution,[],[f1648,f355])).

fof(f1648,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_221 ),
    inference(subsumption_resolution,[],[f1647,f1535])).

fof(f1647,plain,
    ( v15_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1646,f348])).

fof(f1646,plain,
    ( v2_struct_0(sK0)
    | v15_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1645,f341])).

fof(f1645,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1644,f334])).

fof(f1644,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1643,f327])).

fof(f1643,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1616,f362])).

fof(f1616,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_18 ),
    inference(resolution,[],[f389,f746])).

fof(f746,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v15_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f745,f216])).

fof(f745,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v15_lattices(X0)
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f744,f217])).

fof(f744,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v15_lattices(X0)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f743,f249])).

fof(f743,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | v15_lattices(X0)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(resolution,[],[f306,f250])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | v15_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f305,f216])).

fof(f305,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f304,f214])).

fof(f304,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f222,f217])).

fof(f222,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X0) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f130])).

fof(f130,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',t46_filter_1)).

fof(f1642,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | spl10_219 ),
    inference(avatar_contradiction_clause,[],[f1641])).

fof(f1641,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_219 ),
    inference(subsumption_resolution,[],[f1640,f355])).

fof(f1640,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_219 ),
    inference(subsumption_resolution,[],[f1639,f1529])).

fof(f1639,plain,
    ( v16_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1638,f348])).

fof(f1638,plain,
    ( v2_struct_0(sK0)
    | v16_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1637,f341])).

fof(f1637,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1636,f334])).

fof(f1636,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1635,f327])).

fof(f1635,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1615,f362])).

fof(f1615,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl10_18 ),
    inference(resolution,[],[f389,f751])).

fof(f751,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v16_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f750,f216])).

fof(f750,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v16_lattices(X0)
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f749,f217])).

fof(f749,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v16_lattices(X0)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f748,f249])).

fof(f748,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | v16_lattices(X0)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(resolution,[],[f309,f250])).

fof(f309,plain,(
    ! [X0,X1] :
      ( ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | v16_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f308,f216])).

fof(f308,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f307,f214])).

fof(f307,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f221,f217])).

fof(f221,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X0) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f1634,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | spl10_217 ),
    inference(avatar_contradiction_clause,[],[f1633])).

fof(f1633,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_217 ),
    inference(subsumption_resolution,[],[f1632,f355])).

fof(f1632,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_217 ),
    inference(subsumption_resolution,[],[f1631,f1523])).

fof(f1631,plain,
    ( v15_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1630,f348])).

fof(f1630,plain,
    ( v2_struct_0(sK0)
    | v15_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1629,f341])).

fof(f1629,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1628,f334])).

fof(f1628,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1627,f327])).

fof(f1627,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1614,f362])).

fof(f1614,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_18 ),
    inference(resolution,[],[f389,f755])).

fof(f755,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v15_lattices(X1)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f754,f216])).

fof(f754,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v15_lattices(X1)
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f753,f217])).

fof(f753,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v15_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f752,f249])).

fof(f752,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | v15_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(resolution,[],[f312,f250])).

fof(f312,plain,(
    ! [X0,X1] :
      ( ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | v15_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f311,f216])).

fof(f311,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f310,f214])).

fof(f310,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f220,f217])).

fof(f220,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X1) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f1626,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | spl10_215 ),
    inference(avatar_contradiction_clause,[],[f1625])).

fof(f1625,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_215 ),
    inference(subsumption_resolution,[],[f1624,f355])).

fof(f1624,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_215 ),
    inference(subsumption_resolution,[],[f1623,f1517])).

fof(f1623,plain,
    ( v16_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1622,f348])).

fof(f1622,plain,
    ( v2_struct_0(sK0)
    | v16_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1621,f341])).

fof(f1621,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1620,f334])).

fof(f1620,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1619,f327])).

fof(f1619,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1613,f362])).

fof(f1613,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ spl10_18 ),
    inference(resolution,[],[f389,f759])).

fof(f759,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v16_lattices(X1)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f758,f216])).

fof(f758,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v16_lattices(X1)
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f757,f217])).

fof(f757,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v16_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f756,f249])).

fof(f756,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | v16_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(resolution,[],[f315,f250])).

fof(f315,plain,(
    ! [X0,X1] :
      ( ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | v16_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f314,f216])).

fof(f314,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f313,f214])).

fof(f313,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f219,f217])).

fof(f219,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X1) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f1611,plain,
    ( spl10_7
    | ~ spl10_10
    | ~ spl10_22
    | spl10_213 ),
    inference(avatar_contradiction_clause,[],[f1610])).

fof(f1610,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_213 ),
    inference(subsumption_resolution,[],[f1609,f362])).

fof(f1609,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_22
    | ~ spl10_213 ),
    inference(subsumption_resolution,[],[f1608,f403])).

fof(f1608,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_7
    | ~ spl10_213 ),
    inference(subsumption_resolution,[],[f1604,f348])).

fof(f1604,plain,
    ( v2_struct_0(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_213 ),
    inference(resolution,[],[f1511,f248])).

fof(f1602,plain,
    ( spl10_236
    | ~ spl10_50
    | spl10_53
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f918,f538,f531,f510,f503,f1600])).

fof(f1600,plain,
    ( spl10_236
  <=> k7_filter_1(sK5,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK4),u2_lattices(sK5),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK4),u1_lattices(sK5),u1_lattices(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_236])])).

fof(f918,plain,
    ( k7_filter_1(sK5,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK4),u2_lattices(sK5),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK4),u1_lattices(sK5),u1_lattices(sK4)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f908,f539])).

fof(f908,plain,
    ( v2_struct_0(sK5)
    | k7_filter_1(sK5,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK4),u2_lattices(sK5),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK4),u1_lattices(sK5),u1_lattices(sK4)))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_58 ),
    inference(resolution,[],[f788,f532])).

fof(f1595,plain,
    ( spl10_234
    | ~ spl10_50
    | spl10_53 ),
    inference(avatar_split_clause,[],[f917,f510,f503,f1593])).

fof(f1593,plain,
    ( spl10_234
  <=> k7_filter_1(sK4,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK4),u2_lattices(sK4),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK4),u1_lattices(sK4),u1_lattices(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_234])])).

fof(f917,plain,
    ( k7_filter_1(sK4,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK4),u2_lattices(sK4),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK4),u1_lattices(sK4),u1_lattices(sK4)))
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f907,f511])).

fof(f907,plain,
    ( v2_struct_0(sK4)
    | k7_filter_1(sK4,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK4),u2_lattices(sK4),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK4),u1_lattices(sK4),u1_lattices(sK4)))
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(resolution,[],[f788,f504])).

fof(f1588,plain,
    ( spl10_232
    | ~ spl10_24
    | spl10_27
    | ~ spl10_50
    | spl10_53 ),
    inference(avatar_split_clause,[],[f916,f510,f503,f419,f412,f1586])).

fof(f1586,plain,
    ( spl10_232
  <=> k7_filter_1(sK2,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK4),u2_lattices(sK2),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK4),u1_lattices(sK2),u1_lattices(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_232])])).

fof(f916,plain,
    ( k7_filter_1(sK2,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK4),u2_lattices(sK2),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK4),u1_lattices(sK2),u1_lattices(sK4)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f905,f420])).

fof(f905,plain,
    ( v2_struct_0(sK2)
    | k7_filter_1(sK2,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK4),u2_lattices(sK2),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK4),u1_lattices(sK2),u1_lattices(sK4)))
    | ~ spl10_24
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(resolution,[],[f788,f413])).

fof(f1581,plain,
    ( spl10_230
    | ~ spl10_24
    | spl10_27
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f900,f643,f636,f419,f412,f1579])).

fof(f1579,plain,
    ( spl10_230
  <=> k7_filter_1(sK8,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK2),u2_lattices(sK8),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK2),u1_lattices(sK8),u1_lattices(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_230])])).

fof(f900,plain,
    ( k7_filter_1(sK8,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK2),u2_lattices(sK8),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK2),u1_lattices(sK8),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f891,f644])).

fof(f891,plain,
    ( v2_struct_0(sK8)
    | k7_filter_1(sK8,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK2),u2_lattices(sK8),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK2),u1_lattices(sK8),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_88 ),
    inference(resolution,[],[f787,f637])).

fof(f787,plain,
    ( ! [X6] :
        ( ~ l3_lattices(X6)
        | v2_struct_0(X6)
        | k7_filter_1(X6,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(X6),u1_struct_0(sK2),u2_lattices(X6),u2_lattices(sK2)),k6_filter_1(u1_struct_0(X6),u1_struct_0(sK2),u1_lattices(X6),u1_lattices(sK2))) )
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f776,f420])).

fof(f776,plain,
    ( ! [X6] :
        ( ~ l3_lattices(X6)
        | v2_struct_0(sK2)
        | v2_struct_0(X6)
        | k7_filter_1(X6,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(X6),u1_struct_0(sK2),u2_lattices(X6),u2_lattices(sK2)),k6_filter_1(u1_struct_0(X6),u1_struct_0(sK2),u1_lattices(X6),u1_lattices(sK2))) )
    | ~ spl10_24 ),
    inference(resolution,[],[f234,f413])).

fof(f1574,plain,
    ( spl10_228
    | ~ spl10_24
    | spl10_27
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f899,f566,f559,f419,f412,f1572])).

fof(f1572,plain,
    ( spl10_228
  <=> k7_filter_1(sK7,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK2),u2_lattices(sK7),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK2),u1_lattices(sK7),u1_lattices(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_228])])).

fof(f899,plain,
    ( k7_filter_1(sK7,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK2),u2_lattices(sK7),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK2),u1_lattices(sK7),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f890,f567])).

fof(f890,plain,
    ( v2_struct_0(sK7)
    | k7_filter_1(sK7,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK2),u2_lattices(sK7),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK2),u1_lattices(sK7),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_66 ),
    inference(resolution,[],[f787,f560])).

fof(f1567,plain,
    ( spl10_226
    | ~ spl10_24
    | spl10_27
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f898,f538,f531,f419,f412,f1565])).

fof(f1565,plain,
    ( spl10_226
  <=> k7_filter_1(sK5,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK2),u2_lattices(sK5),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK2),u1_lattices(sK5),u1_lattices(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_226])])).

fof(f898,plain,
    ( k7_filter_1(sK5,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK2),u2_lattices(sK5),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK2),u1_lattices(sK5),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f888,f539])).

fof(f888,plain,
    ( v2_struct_0(sK5)
    | k7_filter_1(sK5,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK2),u2_lattices(sK5),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK2),u1_lattices(sK5),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_58 ),
    inference(resolution,[],[f787,f532])).

fof(f1560,plain,
    ( spl10_1
    | ~ spl10_4
    | ~ spl10_12
    | spl10_211 ),
    inference(avatar_contradiction_clause,[],[f1559])).

fof(f1559,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_211 ),
    inference(subsumption_resolution,[],[f1558,f341])).

fof(f1558,plain,
    ( ~ l3_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_211 ),
    inference(subsumption_resolution,[],[f1557,f369])).

fof(f1557,plain,
    ( ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_211 ),
    inference(subsumption_resolution,[],[f1553,f327])).

fof(f1553,plain,
    ( v2_struct_0(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl10_211 ),
    inference(resolution,[],[f1505,f248])).

fof(f1551,plain,
    ( spl10_224
    | ~ spl10_24
    | spl10_27
    | ~ spl10_50
    | spl10_53 ),
    inference(avatar_split_clause,[],[f897,f510,f503,f419,f412,f1549])).

fof(f1549,plain,
    ( spl10_224
  <=> k7_filter_1(sK4,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK2),u2_lattices(sK4),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_lattices(sK4),u1_lattices(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_224])])).

fof(f897,plain,
    ( k7_filter_1(sK4,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK2),u2_lattices(sK4),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_lattices(sK4),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f887,f511])).

fof(f887,plain,
    ( v2_struct_0(sK4)
    | k7_filter_1(sK4,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK2),u2_lattices(sK4),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_lattices(sK4),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_50 ),
    inference(resolution,[],[f787,f504])).

fof(f1544,plain,
    ( spl10_222
    | ~ spl10_24
    | spl10_27 ),
    inference(avatar_split_clause,[],[f896,f419,f412,f1542])).

fof(f1542,plain,
    ( spl10_222
  <=> k7_filter_1(sK2,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK2),u2_lattices(sK2),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_lattices(sK2),u1_lattices(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_222])])).

fof(f896,plain,
    ( k7_filter_1(sK2,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK2),u2_lattices(sK2),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_lattices(sK2),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f885,f420])).

fof(f885,plain,
    ( v2_struct_0(sK2)
    | k7_filter_1(sK2,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK2),u2_lattices(sK2),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_lattices(sK2),u1_lattices(sK2)))
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(resolution,[],[f787,f413])).

fof(f1536,plain,
    ( ~ spl10_211
    | ~ spl10_213
    | ~ spl10_215
    | ~ spl10_217
    | ~ spl10_219
    | ~ spl10_221
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_19 ),
    inference(avatar_split_clause,[],[f1499,f385,f361,f354,f347,f340,f333,f326,f1534,f1528,f1522,f1516,f1510,f1504])).

fof(f385,plain,
    ( spl10_19
  <=> ~ v17_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f1499,plain,
    ( ~ v15_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f1498,f355])).

fof(f1498,plain,
    ( ~ v15_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f1497,f348])).

fof(f1497,plain,
    ( ~ v15_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f1496,f341])).

fof(f1496,plain,
    ( ~ v15_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f1495,f334])).

fof(f1495,plain,
    ( ~ v15_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ v10_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f1494,f327])).

fof(f1494,plain,
    ( ~ v15_lattices(sK0)
    | ~ v16_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ spl10_10
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f1481,f362])).

fof(f1481,plain,
    ( ~ v15_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ spl10_19 ),
    inference(resolution,[],[f870,f386])).

fof(f386,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f385])).

fof(f870,plain,(
    ! [X0,X1] :
      ( v17_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v11_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f867])).

fof(f867,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v17_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f771,f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( v11_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f771,plain,(
    ! [X8,X9] :
      ( ~ v11_lattices(k7_filter_1(X8,X9))
      | ~ v10_lattices(X8)
      | ~ v15_lattices(X8)
      | ~ v16_lattices(X8)
      | ~ l3_lattices(X8)
      | v2_struct_0(X9)
      | ~ v10_lattices(X9)
      | ~ v15_lattices(X9)
      | ~ v16_lattices(X9)
      | ~ l3_lattices(X9)
      | v2_struct_0(X8)
      | v17_lattices(k7_filter_1(X8,X9)) ) ),
    inference(subsumption_resolution,[],[f770,f216])).

fof(f770,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v10_lattices(X8)
      | ~ v15_lattices(X8)
      | ~ v16_lattices(X8)
      | ~ l3_lattices(X8)
      | v2_struct_0(X9)
      | ~ v10_lattices(X9)
      | ~ v15_lattices(X9)
      | ~ v16_lattices(X9)
      | ~ l3_lattices(X9)
      | ~ v11_lattices(k7_filter_1(X8,X9))
      | ~ l3_lattices(k7_filter_1(X8,X9))
      | v17_lattices(k7_filter_1(X8,X9)) ) ),
    inference(subsumption_resolution,[],[f769,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f769,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v10_lattices(X8)
      | ~ v15_lattices(X8)
      | ~ v16_lattices(X8)
      | ~ l3_lattices(X8)
      | v2_struct_0(X9)
      | ~ v10_lattices(X9)
      | ~ v15_lattices(X9)
      | ~ v16_lattices(X9)
      | ~ l3_lattices(X9)
      | ~ v11_lattices(k7_filter_1(X8,X9))
      | ~ v15_lattices(k7_filter_1(X8,X9))
      | ~ l3_lattices(k7_filter_1(X8,X9))
      | v17_lattices(k7_filter_1(X8,X9)) ) ),
    inference(subsumption_resolution,[],[f764,f217])).

fof(f764,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v10_lattices(X8)
      | ~ v15_lattices(X8)
      | ~ v16_lattices(X8)
      | ~ l3_lattices(X8)
      | v2_struct_0(X9)
      | ~ v10_lattices(X9)
      | ~ v15_lattices(X9)
      | ~ v16_lattices(X9)
      | ~ l3_lattices(X9)
      | v2_struct_0(k7_filter_1(X8,X9))
      | ~ v11_lattices(k7_filter_1(X8,X9))
      | ~ v15_lattices(k7_filter_1(X8,X9))
      | ~ l3_lattices(k7_filter_1(X8,X9))
      | v17_lattices(k7_filter_1(X8,X9)) ) ),
    inference(resolution,[],[f226,f247])).

fof(f226,plain,(
    ! [X0,X1] :
      ( v16_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f1460,plain,
    ( spl10_14
    | spl10_208
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f1009,f395,f1458,f371])).

fof(f371,plain,
    ( spl10_14
  <=> v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f1458,plain,
    ( spl10_208
  <=> ! [X5,X4] :
        ( v2_struct_0(X4)
        | v2_struct_0(X5)
        | ~ l3_lattices(X4)
        | ~ l3_lattices(X5)
        | k7_filter_1(X4,k7_filter_1(X5,k7_filter_1(sK0,sK1))) = g3_lattices(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(k7_filter_1(X5,k7_filter_1(sK0,sK1)))),k6_filter_1(u1_struct_0(X4),u1_struct_0(k7_filter_1(X5,k7_filter_1(sK0,sK1))),u2_lattices(X4),u2_lattices(k7_filter_1(X5,k7_filter_1(sK0,sK1)))),k6_filter_1(u1_struct_0(X4),u1_struct_0(k7_filter_1(X5,k7_filter_1(sK0,sK1))),u1_lattices(X4),u1_lattices(k7_filter_1(X5,k7_filter_1(sK0,sK1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_208])])).

fof(f395,plain,
    ( spl10_20
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f1009,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(X4)
        | k7_filter_1(X4,k7_filter_1(X5,k7_filter_1(sK0,sK1))) = g3_lattices(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(k7_filter_1(X5,k7_filter_1(sK0,sK1)))),k6_filter_1(u1_struct_0(X4),u1_struct_0(k7_filter_1(X5,k7_filter_1(sK0,sK1))),u2_lattices(X4),u2_lattices(k7_filter_1(X5,k7_filter_1(sK0,sK1)))),k6_filter_1(u1_struct_0(X4),u1_struct_0(k7_filter_1(X5,k7_filter_1(sK0,sK1))),u1_lattices(X4),u1_lattices(k7_filter_1(X5,k7_filter_1(sK0,sK1)))))
        | ~ l3_lattices(X5)
        | v2_struct_0(k7_filter_1(sK0,sK1))
        | ~ l3_lattices(X4)
        | v2_struct_0(X5) )
    | ~ spl10_20 ),
    inference(resolution,[],[f783,f396])).

fof(f396,plain,
    ( l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f395])).

fof(f783,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X2)
      | v2_struct_0(X0)
      | k7_filter_1(X0,k7_filter_1(X1,X2)) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k7_filter_1(X1,X2))),k6_filter_1(u1_struct_0(X0),u1_struct_0(k7_filter_1(X1,X2)),u2_lattices(X0),u2_lattices(k7_filter_1(X1,X2))),k6_filter_1(u1_struct_0(X0),u1_struct_0(k7_filter_1(X1,X2)),u1_lattices(X0),u1_lattices(k7_filter_1(X1,X2))))
      | ~ l3_lattices(X1)
      | v2_struct_0(X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f772,f217])).

fof(f772,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(k7_filter_1(X1,X2))
      | v2_struct_0(X0)
      | k7_filter_1(X0,k7_filter_1(X1,X2)) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k7_filter_1(X1,X2))),k6_filter_1(u1_struct_0(X0),u1_struct_0(k7_filter_1(X1,X2)),u2_lattices(X0),u2_lattices(k7_filter_1(X1,X2))),k6_filter_1(u1_struct_0(X0),u1_struct_0(k7_filter_1(X1,X2)),u1_lattices(X0),u1_lattices(k7_filter_1(X1,X2))))
      | ~ l3_lattices(X1)
      | v2_struct_0(X2)
      | ~ l3_lattices(X2)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f234,f216])).

fof(f1456,plain,
    ( spl10_206
    | spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f1416,f361,f347,f1454])).

fof(f1454,plain,
    ( spl10_206
  <=> k7_filter_1(k7_filter_1(sK0,sK0),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0),u2_lattices(k7_filter_1(sK0,sK0)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0),u1_lattices(k7_filter_1(sK0,sK0)),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_206])])).

fof(f1416,plain,
    ( k7_filter_1(k7_filter_1(sK0,sK0),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0),u2_lattices(k7_filter_1(sK0,sK0)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0),u1_lattices(k7_filter_1(sK0,sK0)),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1405,f348])).

fof(f1405,plain,
    ( k7_filter_1(k7_filter_1(sK0,sK0),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0),u2_lattices(k7_filter_1(sK0,sK0)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0),u1_lattices(k7_filter_1(sK0,sK0)),u1_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f1337,f362])).

fof(f1337,plain,
    ( ! [X4] :
        ( ~ l3_lattices(X4)
        | k7_filter_1(k7_filter_1(X4,sK0),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(X4,sK0)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(X4,sK0)),u1_struct_0(sK0),u2_lattices(k7_filter_1(X4,sK0)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(X4,sK0)),u1_struct_0(sK0),u1_lattices(k7_filter_1(X4,sK0)),u1_lattices(sK0)))
        | v2_struct_0(X4) )
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1326,f348])).

fof(f1326,plain,
    ( ! [X4] :
        ( ~ l3_lattices(X4)
        | v2_struct_0(sK0)
        | k7_filter_1(k7_filter_1(X4,sK0),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(X4,sK0)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(X4,sK0)),u1_struct_0(sK0),u2_lattices(k7_filter_1(X4,sK0)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(X4,sK0)),u1_struct_0(sK0),u1_lattices(k7_filter_1(X4,sK0)),u1_lattices(sK0)))
        | v2_struct_0(X4) )
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f803,f362])).

fof(f803,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(X1)
        | ~ l3_lattices(X0)
        | v2_struct_0(X1)
        | k7_filter_1(k7_filter_1(X0,X1),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(X0,X1)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(X0,X1)),u1_struct_0(sK0),u2_lattices(k7_filter_1(X0,X1)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(X0,X1)),u1_struct_0(sK0),u1_lattices(k7_filter_1(X0,X1)),u1_lattices(sK0)))
        | v2_struct_0(X0) )
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f792,f217])).

fof(f792,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k7_filter_1(X0,X1))
        | k7_filter_1(k7_filter_1(X0,X1),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(X0,X1)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(X0,X1)),u1_struct_0(sK0),u2_lattices(k7_filter_1(X0,X1)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(X0,X1)),u1_struct_0(sK0),u1_lattices(k7_filter_1(X0,X1)),u1_lattices(sK0)))
        | ~ l3_lattices(X0)
        | v2_struct_0(X1)
        | ~ l3_lattices(X1)
        | v2_struct_0(X0) )
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f785,f216])).

fof(f785,plain,
    ( ! [X4] :
        ( ~ l3_lattices(X4)
        | v2_struct_0(X4)
        | k7_filter_1(X4,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(X4),u1_struct_0(sK0),u2_lattices(X4),u2_lattices(sK0)),k6_filter_1(u1_struct_0(X4),u1_struct_0(sK0),u1_lattices(X4),u1_lattices(sK0))) )
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f774,f348])).

fof(f774,plain,
    ( ! [X4] :
        ( ~ l3_lattices(X4)
        | v2_struct_0(sK0)
        | v2_struct_0(X4)
        | k7_filter_1(X4,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(X4),u1_struct_0(sK0),u2_lattices(X4),u2_lattices(sK0)),k6_filter_1(u1_struct_0(X4),u1_struct_0(sK0),u1_lattices(X4),u1_lattices(sK0))) )
    | ~ spl10_10 ),
    inference(resolution,[],[f234,f362])).

fof(f1429,plain,
    ( spl10_204
    | spl10_15
    | ~ spl10_20
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f1225,f1210,f395,f374,f1427])).

fof(f1427,plain,
    ( spl10_204
  <=> k7_filter_1(k7_filter_1(sK0,sK1),k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_204])])).

fof(f374,plain,
    ( spl10_15
  <=> ~ v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f1210,plain,
    ( spl10_176
  <=> ! [X3] :
        ( ~ l3_lattices(X3)
        | k7_filter_1(X3,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(X3),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(X3),u1_lattices(k7_filter_1(sK0,sK1))))
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_176])])).

fof(f1225,plain,
    ( k7_filter_1(k7_filter_1(sK0,sK1),k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))))
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_176 ),
    inference(subsumption_resolution,[],[f1214,f375])).

fof(f375,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f374])).

fof(f1214,plain,
    ( k7_filter_1(k7_filter_1(sK0,sK1),k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl10_20
    | ~ spl10_176 ),
    inference(resolution,[],[f1211,f396])).

fof(f1211,plain,
    ( ! [X3] :
        ( ~ l3_lattices(X3)
        | k7_filter_1(X3,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(X3),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(X3),u1_lattices(k7_filter_1(sK0,sK1))))
        | v2_struct_0(X3) )
    | ~ spl10_176 ),
    inference(avatar_component_clause,[],[f1210])).

fof(f1323,plain,
    ( spl10_202
    | spl10_14
    | ~ spl10_20
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f969,f643,f636,f395,f371,f1321])).

fof(f1321,plain,
    ( spl10_202
  <=> k7_filter_1(k7_filter_1(sK0,sK1),sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK8),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK8)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK8),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_202])])).

fof(f969,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | k7_filter_1(k7_filter_1(sK0,sK1),sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK8),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK8)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK8),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK8)))
    | ~ spl10_20
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(resolution,[],[f791,f396])).

fof(f1316,plain,
    ( spl10_200
    | spl10_14
    | ~ spl10_20
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f949,f566,f559,f395,f371,f1314])).

fof(f1314,plain,
    ( spl10_200
  <=> k7_filter_1(k7_filter_1(sK0,sK1),sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK7),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK7)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK7),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_200])])).

fof(f949,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | k7_filter_1(k7_filter_1(sK0,sK1),sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK7),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK7)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK7),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK7)))
    | ~ spl10_20
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(resolution,[],[f790,f396])).

fof(f1309,plain,
    ( spl10_198
    | spl10_14
    | ~ spl10_20
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f922,f538,f531,f395,f371,f1307])).

fof(f1307,plain,
    ( spl10_198
  <=> k7_filter_1(k7_filter_1(sK0,sK1),sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK5),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK5)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK5),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_198])])).

fof(f922,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | k7_filter_1(k7_filter_1(sK0,sK1),sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK5),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK5)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK5),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK5)))
    | ~ spl10_20
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(resolution,[],[f789,f396])).

fof(f1302,plain,
    ( spl10_196
    | spl10_14
    | ~ spl10_20
    | ~ spl10_50
    | spl10_53 ),
    inference(avatar_split_clause,[],[f902,f510,f503,f395,f371,f1300])).

fof(f1300,plain,
    ( spl10_196
  <=> k7_filter_1(k7_filter_1(sK0,sK1),sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK4),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK4)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK4),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_196])])).

fof(f902,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | k7_filter_1(k7_filter_1(sK0,sK1),sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK4),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK4)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK4),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK4)))
    | ~ spl10_20
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(resolution,[],[f788,f396])).

fof(f1295,plain,
    ( spl10_194
    | spl10_14
    | ~ spl10_20
    | ~ spl10_24
    | spl10_27 ),
    inference(avatar_split_clause,[],[f882,f419,f412,f395,f371,f1293])).

fof(f1293,plain,
    ( spl10_194
  <=> k7_filter_1(k7_filter_1(sK0,sK1),sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK2),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK2)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK2),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_194])])).

fof(f882,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | k7_filter_1(k7_filter_1(sK0,sK1),sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK2),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK2)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK2),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK2)))
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(resolution,[],[f787,f396])).

fof(f1288,plain,
    ( spl10_192
    | spl10_14
    | spl10_1
    | ~ spl10_4
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f813,f395,f340,f326,f371,f1286])).

fof(f1286,plain,
    ( spl10_192
  <=> k7_filter_1(k7_filter_1(sK0,sK1),sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK1),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK1)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK1),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_192])])).

fof(f813,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | k7_filter_1(k7_filter_1(sK0,sK1),sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK1),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK1)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK1),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_20 ),
    inference(resolution,[],[f786,f396])).

fof(f786,plain,
    ( ! [X5] :
        ( ~ l3_lattices(X5)
        | v2_struct_0(X5)
        | k7_filter_1(X5,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(X5),u1_struct_0(sK1),u2_lattices(X5),u2_lattices(sK1)),k6_filter_1(u1_struct_0(X5),u1_struct_0(sK1),u1_lattices(X5),u1_lattices(sK1))) )
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f775,f327])).

fof(f775,plain,
    ( ! [X5] :
        ( ~ l3_lattices(X5)
        | v2_struct_0(sK1)
        | v2_struct_0(X5)
        | k7_filter_1(X5,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(X5),u1_struct_0(sK1),u2_lattices(X5),u2_lattices(sK1)),k6_filter_1(u1_struct_0(X5),u1_struct_0(sK1),u1_lattices(X5),u1_lattices(sK1))) )
    | ~ spl10_4 ),
    inference(resolution,[],[f234,f341])).

fof(f1281,plain,
    ( spl10_190
    | ~ spl10_88
    | spl10_91
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f1232,f1210,f643,f636,f1279])).

fof(f1279,plain,
    ( spl10_190
  <=> k7_filter_1(sK8,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK8),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK8),u1_lattices(k7_filter_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_190])])).

fof(f1232,plain,
    ( k7_filter_1(sK8,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK8),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK8),u1_lattices(k7_filter_1(sK0,sK1))))
    | ~ spl10_88
    | ~ spl10_91
    | ~ spl10_176 ),
    inference(subsumption_resolution,[],[f1223,f644])).

fof(f1223,plain,
    ( k7_filter_1(sK8,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK8),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK8),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK8),u1_lattices(k7_filter_1(sK0,sK1))))
    | v2_struct_0(sK8)
    | ~ spl10_88
    | ~ spl10_176 ),
    inference(resolution,[],[f1211,f637])).

fof(f1274,plain,
    ( spl10_188
    | ~ spl10_66
    | spl10_69
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f1231,f1210,f566,f559,f1272])).

fof(f1272,plain,
    ( spl10_188
  <=> k7_filter_1(sK7,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK7),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK7),u1_lattices(k7_filter_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_188])])).

fof(f1231,plain,
    ( k7_filter_1(sK7,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK7),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK7),u1_lattices(k7_filter_1(sK0,sK1))))
    | ~ spl10_66
    | ~ spl10_69
    | ~ spl10_176 ),
    inference(subsumption_resolution,[],[f1222,f567])).

fof(f1222,plain,
    ( k7_filter_1(sK7,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK7),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK7),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK7),u1_lattices(k7_filter_1(sK0,sK1))))
    | v2_struct_0(sK7)
    | ~ spl10_66
    | ~ spl10_176 ),
    inference(resolution,[],[f1211,f560])).

fof(f1267,plain,
    ( spl10_186
    | ~ spl10_58
    | spl10_61
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f1230,f1210,f538,f531,f1265])).

fof(f1265,plain,
    ( spl10_186
  <=> k7_filter_1(sK5,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK5),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK5),u1_lattices(k7_filter_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_186])])).

fof(f1230,plain,
    ( k7_filter_1(sK5,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK5),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK5),u1_lattices(k7_filter_1(sK0,sK1))))
    | ~ spl10_58
    | ~ spl10_61
    | ~ spl10_176 ),
    inference(subsumption_resolution,[],[f1220,f539])).

fof(f1220,plain,
    ( k7_filter_1(sK5,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK5),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK5),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK5),u1_lattices(k7_filter_1(sK0,sK1))))
    | v2_struct_0(sK5)
    | ~ spl10_58
    | ~ spl10_176 ),
    inference(resolution,[],[f1211,f532])).

fof(f1260,plain,
    ( spl10_184
    | ~ spl10_50
    | spl10_53
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f1229,f1210,f510,f503,f1258])).

fof(f1258,plain,
    ( spl10_184
  <=> k7_filter_1(sK4,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK4),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK4),u1_lattices(k7_filter_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_184])])).

fof(f1229,plain,
    ( k7_filter_1(sK4,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK4),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK4),u1_lattices(k7_filter_1(sK0,sK1))))
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_176 ),
    inference(subsumption_resolution,[],[f1219,f511])).

fof(f1219,plain,
    ( k7_filter_1(sK4,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK4),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK4),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK4),u1_lattices(k7_filter_1(sK0,sK1))))
    | v2_struct_0(sK4)
    | ~ spl10_50
    | ~ spl10_176 ),
    inference(resolution,[],[f1211,f504])).

fof(f1253,plain,
    ( spl10_182
    | ~ spl10_24
    | spl10_27
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f1228,f1210,f419,f412,f1251])).

fof(f1251,plain,
    ( spl10_182
  <=> k7_filter_1(sK2,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK2),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK2),u1_lattices(k7_filter_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_182])])).

fof(f1228,plain,
    ( k7_filter_1(sK2,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK2),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK2),u1_lattices(k7_filter_1(sK0,sK1))))
    | ~ spl10_24
    | ~ spl10_27
    | ~ spl10_176 ),
    inference(subsumption_resolution,[],[f1217,f420])).

fof(f1217,plain,
    ( k7_filter_1(sK2,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK2),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK2),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK2),u1_lattices(k7_filter_1(sK0,sK1))))
    | v2_struct_0(sK2)
    | ~ spl10_24
    | ~ spl10_176 ),
    inference(resolution,[],[f1211,f413])).

fof(f1246,plain,
    ( spl10_180
    | spl10_1
    | ~ spl10_4
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f1227,f1210,f340,f326,f1244])).

fof(f1244,plain,
    ( spl10_180
  <=> k7_filter_1(sK1,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK1),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK1),u1_lattices(k7_filter_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_180])])).

fof(f1227,plain,
    ( k7_filter_1(sK1,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK1),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK1),u1_lattices(k7_filter_1(sK0,sK1))))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_176 ),
    inference(subsumption_resolution,[],[f1216,f327])).

fof(f1216,plain,
    ( k7_filter_1(sK1,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK1),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK1),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK1),u1_lattices(k7_filter_1(sK0,sK1))))
    | v2_struct_0(sK1)
    | ~ spl10_4
    | ~ spl10_176 ),
    inference(resolution,[],[f1211,f341])).

fof(f1239,plain,
    ( spl10_178
    | spl10_7
    | ~ spl10_10
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f1226,f1210,f361,f347,f1237])).

fof(f1237,plain,
    ( spl10_178
  <=> k7_filter_1(sK0,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK0),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK0),u1_lattices(k7_filter_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_178])])).

fof(f1226,plain,
    ( k7_filter_1(sK0,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK0),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK0),u1_lattices(k7_filter_1(sK0,sK1))))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_176 ),
    inference(subsumption_resolution,[],[f1215,f348])).

fof(f1215,plain,
    ( k7_filter_1(sK0,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(sK0),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(sK0),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(sK0),u1_lattices(k7_filter_1(sK0,sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_10
    | ~ spl10_176 ),
    inference(resolution,[],[f1211,f362])).

fof(f1212,plain,
    ( spl10_14
    | spl10_176
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f773,f395,f1210,f371])).

fof(f773,plain,
    ( ! [X3] :
        ( ~ l3_lattices(X3)
        | v2_struct_0(k7_filter_1(sK0,sK1))
        | v2_struct_0(X3)
        | k7_filter_1(X3,k7_filter_1(sK0,sK1)) = g3_lattices(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(X3),u2_lattices(k7_filter_1(sK0,sK1))),k6_filter_1(u1_struct_0(X3),u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(X3),u1_lattices(k7_filter_1(sK0,sK1)))) )
    | ~ spl10_20 ),
    inference(resolution,[],[f234,f396])).

fof(f1208,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10
    | ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f1207])).

fof(f1207,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f1206,f348])).

fof(f1206,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f1205,f341])).

fof(f1205,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f1204,f327])).

fof(f1204,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_10
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f1203,f362])).

fof(f1203,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14 ),
    inference(resolution,[],[f372,f217])).

fof(f372,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f371])).

fof(f1202,plain,
    ( spl10_174
    | spl10_7
    | ~ spl10_10
    | spl10_15
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f804,f395,f374,f361,f347,f1200])).

fof(f1200,plain,
    ( spl10_174
  <=> k7_filter_1(k7_filter_1(sK0,sK1),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_174])])).

fof(f804,plain,
    ( k7_filter_1(k7_filter_1(sK0,sK1),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_15
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f793,f375])).

fof(f793,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | k7_filter_1(k7_filter_1(sK0,sK1),sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0),u2_lattices(k7_filter_1(sK0,sK1)),u2_lattices(sK0)),k6_filter_1(u1_struct_0(k7_filter_1(sK0,sK1)),u1_struct_0(sK0),u1_lattices(k7_filter_1(sK0,sK1)),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_20 ),
    inference(resolution,[],[f785,f396])).

fof(f1195,plain,
    ( spl10_172
    | spl10_122
    | spl10_1
    | ~ spl10_4
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f820,f552,f340,f326,f1002,f1193])).

fof(f1193,plain,
    ( spl10_172
  <=> k7_filter_1(sK6,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK6),u1_struct_0(sK1),u2_lattices(sK6),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK6),u1_struct_0(sK1),u1_lattices(sK6),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_172])])).

fof(f1002,plain,
    ( spl10_122
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f552,plain,
    ( spl10_64
  <=> l3_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f820,plain,
    ( v2_struct_0(sK6)
    | k7_filter_1(sK6,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK6),u1_struct_0(sK1),u2_lattices(sK6),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK6),u1_struct_0(sK1),u1_lattices(sK6),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_64 ),
    inference(resolution,[],[f786,f553])).

fof(f553,plain,
    ( l3_lattices(sK6)
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f552])).

fof(f1188,plain,
    ( spl10_170
    | spl10_118
    | spl10_1
    | ~ spl10_4
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f817,f489,f340,f326,f992,f1186])).

fof(f1186,plain,
    ( spl10_170
  <=> k7_filter_1(sK3,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK3),u1_struct_0(sK1),u2_lattices(sK3),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK3),u1_struct_0(sK1),u1_lattices(sK3),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_170])])).

fof(f992,plain,
    ( spl10_118
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).

fof(f489,plain,
    ( spl10_46
  <=> l3_lattices(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f817,plain,
    ( v2_struct_0(sK3)
    | k7_filter_1(sK3,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK3),u1_struct_0(sK1),u2_lattices(sK3),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK3),u1_struct_0(sK1),u1_lattices(sK3),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_46 ),
    inference(resolution,[],[f786,f490])).

fof(f490,plain,
    ( l3_lattices(sK3)
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f489])).

fof(f1181,plain,
    ( spl10_168
    | spl10_122
    | spl10_7
    | ~ spl10_10
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f800,f552,f361,f347,f1002,f1179])).

fof(f1179,plain,
    ( spl10_168
  <=> k7_filter_1(sK6,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK6),u1_struct_0(sK0),u2_lattices(sK6),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK6),u1_struct_0(sK0),u1_lattices(sK6),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_168])])).

fof(f800,plain,
    ( v2_struct_0(sK6)
    | k7_filter_1(sK6,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK6),u1_struct_0(sK0),u2_lattices(sK6),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK6),u1_struct_0(sK0),u1_lattices(sK6),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_64 ),
    inference(resolution,[],[f785,f553])).

fof(f1174,plain,
    ( spl10_166
    | spl10_118
    | spl10_7
    | ~ spl10_10
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f797,f489,f361,f347,f992,f1172])).

fof(f1172,plain,
    ( spl10_166
  <=> k7_filter_1(sK3,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK3),u1_struct_0(sK0),u2_lattices(sK3),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK3),u1_struct_0(sK0),u1_lattices(sK3),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_166])])).

fof(f797,plain,
    ( v2_struct_0(sK3)
    | k7_filter_1(sK3,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK3),u1_struct_0(sK0),u2_lattices(sK3),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK3),u1_struct_0(sK0),u1_lattices(sK3),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_46 ),
    inference(resolution,[],[f785,f490])).

fof(f1167,plain,
    ( spl10_164
    | spl10_1
    | ~ spl10_4
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f982,f643,f636,f340,f326,f1165])).

fof(f1165,plain,
    ( spl10_164
  <=> k7_filter_1(sK1,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK8),u2_lattices(sK1),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK8),u1_lattices(sK1),u1_lattices(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_164])])).

fof(f982,plain,
    ( k7_filter_1(sK1,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK8),u2_lattices(sK1),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK8),u1_lattices(sK1),u1_lattices(sK8)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f971,f327])).

fof(f971,plain,
    ( v2_struct_0(sK1)
    | k7_filter_1(sK1,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK8),u2_lattices(sK1),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK8),u1_lattices(sK1),u1_lattices(sK8)))
    | ~ spl10_4
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(resolution,[],[f791,f341])).

fof(f1160,plain,
    ( spl10_162
    | spl10_7
    | ~ spl10_10
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f981,f643,f636,f361,f347,f1158])).

fof(f1158,plain,
    ( spl10_162
  <=> k7_filter_1(sK0,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK8),u2_lattices(sK0),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK8),u1_lattices(sK0),u1_lattices(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).

fof(f981,plain,
    ( k7_filter_1(sK0,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK8),u2_lattices(sK0),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK8),u1_lattices(sK0),u1_lattices(sK8)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f970,f348])).

fof(f970,plain,
    ( v2_struct_0(sK0)
    | k7_filter_1(sK0,sK8) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK8)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK8),u2_lattices(sK0),u2_lattices(sK8)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK8),u1_lattices(sK0),u1_lattices(sK8)))
    | ~ spl10_10
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(resolution,[],[f791,f362])).

fof(f1153,plain,
    ( spl10_160
    | spl10_1
    | ~ spl10_4
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f962,f566,f559,f340,f326,f1151])).

fof(f1151,plain,
    ( spl10_160
  <=> k7_filter_1(sK1,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK7),u2_lattices(sK1),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK7),u1_lattices(sK1),u1_lattices(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_160])])).

fof(f962,plain,
    ( k7_filter_1(sK1,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK7),u2_lattices(sK1),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK7),u1_lattices(sK1),u1_lattices(sK7)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f951,f327])).

fof(f951,plain,
    ( v2_struct_0(sK1)
    | k7_filter_1(sK1,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK7),u2_lattices(sK1),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK7),u1_lattices(sK1),u1_lattices(sK7)))
    | ~ spl10_4
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(resolution,[],[f790,f341])).

fof(f1146,plain,
    ( spl10_158
    | spl10_7
    | ~ spl10_10
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f961,f566,f559,f361,f347,f1144])).

fof(f1144,plain,
    ( spl10_158
  <=> k7_filter_1(sK0,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK7),u2_lattices(sK0),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK7),u1_lattices(sK0),u1_lattices(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_158])])).

fof(f961,plain,
    ( k7_filter_1(sK0,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK7),u2_lattices(sK0),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK7),u1_lattices(sK0),u1_lattices(sK7)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f950,f348])).

fof(f950,plain,
    ( v2_struct_0(sK0)
    | k7_filter_1(sK0,sK7) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK7)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK7),u2_lattices(sK0),u2_lattices(sK7)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK7),u1_lattices(sK0),u1_lattices(sK7)))
    | ~ spl10_10
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(resolution,[],[f790,f362])).

fof(f1139,plain,
    ( spl10_156
    | spl10_1
    | ~ spl10_4
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f935,f538,f531,f340,f326,f1137])).

fof(f1137,plain,
    ( spl10_156
  <=> k7_filter_1(sK1,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK5),u2_lattices(sK1),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK5),u1_lattices(sK1),u1_lattices(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_156])])).

fof(f935,plain,
    ( k7_filter_1(sK1,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK5),u2_lattices(sK1),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK5),u1_lattices(sK1),u1_lattices(sK5)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f924,f327])).

fof(f924,plain,
    ( v2_struct_0(sK1)
    | k7_filter_1(sK1,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK5),u2_lattices(sK1),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK5),u1_lattices(sK1),u1_lattices(sK5)))
    | ~ spl10_4
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(resolution,[],[f789,f341])).

fof(f1132,plain,
    ( spl10_154
    | spl10_7
    | ~ spl10_10
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f934,f538,f531,f361,f347,f1130])).

fof(f1130,plain,
    ( spl10_154
  <=> k7_filter_1(sK0,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK5),u2_lattices(sK0),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK5),u1_lattices(sK0),u1_lattices(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f934,plain,
    ( k7_filter_1(sK0,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK5),u2_lattices(sK0),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK5),u1_lattices(sK0),u1_lattices(sK5)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f923,f348])).

fof(f923,plain,
    ( v2_struct_0(sK0)
    | k7_filter_1(sK0,sK5) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK5),u2_lattices(sK0),u2_lattices(sK5)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK5),u1_lattices(sK0),u1_lattices(sK5)))
    | ~ spl10_10
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(resolution,[],[f789,f362])).

fof(f1125,plain,
    ( spl10_152
    | spl10_1
    | ~ spl10_4
    | ~ spl10_50
    | spl10_53 ),
    inference(avatar_split_clause,[],[f915,f510,f503,f340,f326,f1123])).

fof(f1123,plain,
    ( spl10_152
  <=> k7_filter_1(sK1,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK4),u2_lattices(sK1),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK4),u1_lattices(sK1),u1_lattices(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_152])])).

fof(f915,plain,
    ( k7_filter_1(sK1,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK4),u2_lattices(sK1),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK4),u1_lattices(sK1),u1_lattices(sK4)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f904,f327])).

fof(f904,plain,
    ( v2_struct_0(sK1)
    | k7_filter_1(sK1,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK4),u2_lattices(sK1),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK4),u1_lattices(sK1),u1_lattices(sK4)))
    | ~ spl10_4
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(resolution,[],[f788,f341])).

fof(f1118,plain,
    ( spl10_150
    | spl10_7
    | ~ spl10_10
    | ~ spl10_50
    | spl10_53 ),
    inference(avatar_split_clause,[],[f914,f510,f503,f361,f347,f1116])).

fof(f1116,plain,
    ( spl10_150
  <=> k7_filter_1(sK0,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK4),u2_lattices(sK0),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK4),u1_lattices(sK0),u1_lattices(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_150])])).

fof(f914,plain,
    ( k7_filter_1(sK0,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK4),u2_lattices(sK0),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK4),u1_lattices(sK0),u1_lattices(sK4)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f903,f348])).

fof(f903,plain,
    ( v2_struct_0(sK0)
    | k7_filter_1(sK0,sK4) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK4)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK4),u2_lattices(sK0),u2_lattices(sK4)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK4),u1_lattices(sK0),u1_lattices(sK4)))
    | ~ spl10_10
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(resolution,[],[f788,f362])).

fof(f1111,plain,
    ( spl10_148
    | spl10_1
    | ~ spl10_4
    | ~ spl10_24
    | spl10_27 ),
    inference(avatar_split_clause,[],[f895,f419,f412,f340,f326,f1109])).

fof(f1109,plain,
    ( spl10_148
  <=> k7_filter_1(sK1,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK2),u2_lattices(sK1),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK2),u1_lattices(sK1),u1_lattices(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_148])])).

fof(f895,plain,
    ( k7_filter_1(sK1,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK2),u2_lattices(sK1),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK2),u1_lattices(sK1),u1_lattices(sK2)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f884,f327])).

fof(f884,plain,
    ( v2_struct_0(sK1)
    | k7_filter_1(sK1,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK2),u2_lattices(sK1),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK2),u1_lattices(sK1),u1_lattices(sK2)))
    | ~ spl10_4
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(resolution,[],[f787,f341])).

fof(f1104,plain,
    ( spl10_146
    | spl10_7
    | ~ spl10_10
    | ~ spl10_24
    | spl10_27 ),
    inference(avatar_split_clause,[],[f894,f419,f412,f361,f347,f1102])).

fof(f1102,plain,
    ( spl10_146
  <=> k7_filter_1(sK0,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK2),u2_lattices(sK0),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK2),u1_lattices(sK0),u1_lattices(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_146])])).

fof(f894,plain,
    ( k7_filter_1(sK0,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK2),u2_lattices(sK0),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK2),u1_lattices(sK0),u1_lattices(sK2)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f883,f348])).

fof(f883,plain,
    ( v2_struct_0(sK0)
    | k7_filter_1(sK0,sK2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK2),u2_lattices(sK0),u2_lattices(sK2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK2),u1_lattices(sK0),u1_lattices(sK2)))
    | ~ spl10_10
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(resolution,[],[f787,f362])).

fof(f1097,plain,
    ( spl10_144
    | spl10_1
    | ~ spl10_4
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f831,f643,f636,f340,f326,f1095])).

fof(f1095,plain,
    ( spl10_144
  <=> k7_filter_1(sK8,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK1),u2_lattices(sK8),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK1),u1_lattices(sK8),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_144])])).

fof(f831,plain,
    ( k7_filter_1(sK8,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK1),u2_lattices(sK8),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK1),u1_lattices(sK8),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f822,f644])).

fof(f822,plain,
    ( v2_struct_0(sK8)
    | k7_filter_1(sK8,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK1),u2_lattices(sK8),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK1),u1_lattices(sK8),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_88 ),
    inference(resolution,[],[f786,f637])).

fof(f1090,plain,
    ( spl10_142
    | spl10_1
    | ~ spl10_4
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f830,f566,f559,f340,f326,f1088])).

fof(f1088,plain,
    ( spl10_142
  <=> k7_filter_1(sK7,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK1),u2_lattices(sK7),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK1),u1_lattices(sK7),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_142])])).

fof(f830,plain,
    ( k7_filter_1(sK7,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK1),u2_lattices(sK7),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK1),u1_lattices(sK7),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f821,f567])).

fof(f821,plain,
    ( v2_struct_0(sK7)
    | k7_filter_1(sK7,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK1),u2_lattices(sK7),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK1),u1_lattices(sK7),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_66 ),
    inference(resolution,[],[f786,f560])).

fof(f1083,plain,
    ( spl10_140
    | spl10_1
    | ~ spl10_4
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f829,f538,f531,f340,f326,f1081])).

fof(f1081,plain,
    ( spl10_140
  <=> k7_filter_1(sK5,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK1),u2_lattices(sK5),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK1),u1_lattices(sK5),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f829,plain,
    ( k7_filter_1(sK5,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK1),u2_lattices(sK5),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK1),u1_lattices(sK5),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f819,f539])).

fof(f819,plain,
    ( v2_struct_0(sK5)
    | k7_filter_1(sK5,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK1),u2_lattices(sK5),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK1),u1_lattices(sK5),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_58 ),
    inference(resolution,[],[f786,f532])).

fof(f1076,plain,
    ( spl10_138
    | spl10_1
    | ~ spl10_4
    | ~ spl10_50
    | spl10_53 ),
    inference(avatar_split_clause,[],[f828,f510,f503,f340,f326,f1074])).

fof(f1074,plain,
    ( spl10_138
  <=> k7_filter_1(sK4,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK1),u2_lattices(sK4),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK1),u1_lattices(sK4),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_138])])).

fof(f828,plain,
    ( k7_filter_1(sK4,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK1),u2_lattices(sK4),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK1),u1_lattices(sK4),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f818,f511])).

fof(f818,plain,
    ( v2_struct_0(sK4)
    | k7_filter_1(sK4,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK1),u2_lattices(sK4),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK1),u1_lattices(sK4),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_50 ),
    inference(resolution,[],[f786,f504])).

fof(f1069,plain,
    ( spl10_136
    | spl10_1
    | ~ spl10_4
    | ~ spl10_24
    | spl10_27 ),
    inference(avatar_split_clause,[],[f827,f419,f412,f340,f326,f1067])).

fof(f1067,plain,
    ( spl10_136
  <=> k7_filter_1(sK2,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK1),u2_lattices(sK2),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK1),u1_lattices(sK2),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f827,plain,
    ( k7_filter_1(sK2,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK1),u2_lattices(sK2),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK1),u1_lattices(sK2),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f816,f420])).

fof(f816,plain,
    ( v2_struct_0(sK2)
    | k7_filter_1(sK2,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK1),u2_lattices(sK2),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK1),u1_lattices(sK2),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_24 ),
    inference(resolution,[],[f786,f413])).

fof(f1062,plain,
    ( spl10_134
    | spl10_1
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f826,f340,f326,f1060])).

fof(f1060,plain,
    ( spl10_134
  <=> k7_filter_1(sK1,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f826,plain,
    ( k7_filter_1(sK1,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f815,f327])).

fof(f815,plain,
    ( v2_struct_0(sK1)
    | k7_filter_1(sK1,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f786,f341])).

fof(f1055,plain,
    ( spl10_132
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f825,f361,f347,f340,f326,f1053])).

fof(f1053,plain,
    ( spl10_132
  <=> k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f825,plain,
    ( k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f814,f348])).

fof(f814,plain,
    ( v2_struct_0(sK0)
    | k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(resolution,[],[f786,f362])).

fof(f1048,plain,
    ( spl10_130
    | spl10_7
    | ~ spl10_10
    | ~ spl10_88
    | spl10_91 ),
    inference(avatar_split_clause,[],[f811,f643,f636,f361,f347,f1046])).

fof(f1046,plain,
    ( spl10_130
  <=> k7_filter_1(sK8,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK0),u2_lattices(sK8),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK0),u1_lattices(sK8),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f811,plain,
    ( k7_filter_1(sK8,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK0),u2_lattices(sK8),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK0),u1_lattices(sK8),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_88
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f802,f644])).

fof(f802,plain,
    ( v2_struct_0(sK8)
    | k7_filter_1(sK8,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK0),u2_lattices(sK8),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK8),u1_struct_0(sK0),u1_lattices(sK8),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_88 ),
    inference(resolution,[],[f785,f637])).

fof(f1041,plain,
    ( spl10_128
    | spl10_7
    | ~ spl10_10
    | ~ spl10_66
    | spl10_69 ),
    inference(avatar_split_clause,[],[f810,f566,f559,f361,f347,f1039])).

fof(f1039,plain,
    ( spl10_128
  <=> k7_filter_1(sK7,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK0),u2_lattices(sK7),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK0),u1_lattices(sK7),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f810,plain,
    ( k7_filter_1(sK7,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK0),u2_lattices(sK7),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK0),u1_lattices(sK7),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_66
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f801,f567])).

fof(f801,plain,
    ( v2_struct_0(sK7)
    | k7_filter_1(sK7,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK0),u2_lattices(sK7),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK7),u1_struct_0(sK0),u1_lattices(sK7),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_66 ),
    inference(resolution,[],[f785,f560])).

fof(f1034,plain,
    ( spl10_126
    | spl10_7
    | ~ spl10_10
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f809,f538,f531,f361,f347,f1032])).

fof(f1032,plain,
    ( spl10_126
  <=> k7_filter_1(sK5,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK0),u2_lattices(sK5),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK0),u1_lattices(sK5),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f809,plain,
    ( k7_filter_1(sK5,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK0),u2_lattices(sK5),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK0),u1_lattices(sK5),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f799,f539])).

fof(f799,plain,
    ( v2_struct_0(sK5)
    | k7_filter_1(sK5,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK0),u2_lattices(sK5),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK5),u1_struct_0(sK0),u1_lattices(sK5),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_58 ),
    inference(resolution,[],[f785,f532])).

fof(f1007,plain,
    ( spl10_122
    | spl10_124
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f780,f552,f1005,f1002])).

fof(f1005,plain,
    ( spl10_124
  <=> ! [X10] :
        ( ~ l3_lattices(X10)
        | k7_filter_1(X10,sK6) = g3_lattices(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK6)),k6_filter_1(u1_struct_0(X10),u1_struct_0(sK6),u2_lattices(X10),u2_lattices(sK6)),k6_filter_1(u1_struct_0(X10),u1_struct_0(sK6),u1_lattices(X10),u1_lattices(sK6)))
        | v2_struct_0(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f780,plain,
    ( ! [X10] :
        ( ~ l3_lattices(X10)
        | v2_struct_0(sK6)
        | v2_struct_0(X10)
        | k7_filter_1(X10,sK6) = g3_lattices(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK6)),k6_filter_1(u1_struct_0(X10),u1_struct_0(sK6),u2_lattices(X10),u2_lattices(sK6)),k6_filter_1(u1_struct_0(X10),u1_struct_0(sK6),u1_lattices(X10),u1_lattices(sK6))) )
    | ~ spl10_64 ),
    inference(resolution,[],[f234,f553])).

fof(f997,plain,
    ( spl10_118
    | spl10_120
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f777,f489,f995,f992])).

fof(f995,plain,
    ( spl10_120
  <=> ! [X7] :
        ( ~ l3_lattices(X7)
        | k7_filter_1(X7,sK3) = g3_lattices(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3)),k6_filter_1(u1_struct_0(X7),u1_struct_0(sK3),u2_lattices(X7),u2_lattices(sK3)),k6_filter_1(u1_struct_0(X7),u1_struct_0(sK3),u1_lattices(X7),u1_lattices(sK3)))
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_120])])).

fof(f777,plain,
    ( ! [X7] :
        ( ~ l3_lattices(X7)
        | v2_struct_0(sK3)
        | v2_struct_0(X7)
        | k7_filter_1(X7,sK3) = g3_lattices(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3)),k6_filter_1(u1_struct_0(X7),u1_struct_0(sK3),u2_lattices(X7),u2_lattices(sK3)),k6_filter_1(u1_struct_0(X7),u1_struct_0(sK3),u1_lattices(X7),u1_lattices(sK3))) )
    | ~ spl10_46 ),
    inference(resolution,[],[f234,f490])).

fof(f947,plain,
    ( spl10_116
    | spl10_7
    | ~ spl10_10
    | ~ spl10_50
    | spl10_53 ),
    inference(avatar_split_clause,[],[f808,f510,f503,f361,f347,f945])).

fof(f945,plain,
    ( spl10_116
  <=> k7_filter_1(sK4,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK0),u2_lattices(sK4),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK0),u1_lattices(sK4),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f808,plain,
    ( k7_filter_1(sK4,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK0),u2_lattices(sK4),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK0),u1_lattices(sK4),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_50
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f798,f511])).

fof(f798,plain,
    ( v2_struct_0(sK4)
    | k7_filter_1(sK4,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK0),u2_lattices(sK4),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK4),u1_struct_0(sK0),u1_lattices(sK4),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_50 ),
    inference(resolution,[],[f785,f504])).

fof(f880,plain,
    ( spl10_114
    | spl10_7
    | ~ spl10_10
    | ~ spl10_24
    | spl10_27 ),
    inference(avatar_split_clause,[],[f807,f419,f412,f361,f347,f878])).

fof(f878,plain,
    ( spl10_114
  <=> k7_filter_1(sK2,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK0),u2_lattices(sK2),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_lattices(sK2),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f807,plain,
    ( k7_filter_1(sK2,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK0),u2_lattices(sK2),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_lattices(sK2),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f796,f420])).

fof(f796,plain,
    ( v2_struct_0(sK2)
    | k7_filter_1(sK2,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK0),u2_lattices(sK2),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_lattices(sK2),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_24 ),
    inference(resolution,[],[f785,f413])).

fof(f866,plain,
    ( spl10_112
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f806,f361,f347,f340,f326,f864])).

fof(f864,plain,
    ( spl10_112
  <=> k7_filter_1(sK1,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK0),u2_lattices(sK1),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_lattices(sK1),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_112])])).

fof(f806,plain,
    ( k7_filter_1(sK1,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK0),u2_lattices(sK1),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_lattices(sK1),u1_lattices(sK0)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f795,f327])).

fof(f795,plain,
    ( v2_struct_0(sK1)
    | k7_filter_1(sK1,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK0),u2_lattices(sK1),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_lattices(sK1),u1_lattices(sK0)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f785,f341])).

fof(f859,plain,
    ( spl10_110
    | spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f805,f361,f347,f857])).

fof(f857,plain,
    ( spl10_110
  <=> k7_filter_1(sK0,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_110])])).

fof(f805,plain,
    ( k7_filter_1(sK0,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f794,f348])).

fof(f794,plain,
    ( v2_struct_0(sK0)
    | k7_filter_1(sK0,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)))
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f785,f362])).

fof(f717,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_10
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f716])).

fof(f716,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f715,f348])).

fof(f715,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f714,f341])).

fof(f714,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f713,f327])).

fof(f713,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f712,f362])).

fof(f712,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl10_21 ),
    inference(resolution,[],[f216,f393])).

fof(f393,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl10_21
  <=> ~ l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f709,plain,
    ( ~ spl10_13
    | ~ spl10_23
    | ~ spl10_21
    | ~ spl10_19
    | ~ spl10_17
    | spl10_14 ),
    inference(avatar_split_clause,[],[f303,f371,f378,f385,f392,f399,f365])).

fof(f365,plain,
    ( spl10_13
  <=> ~ v17_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f399,plain,
    ( spl10_23
  <=> ~ v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f303,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f302,f209])).

fof(f209,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f136])).

fof(f136,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( l3_lattices(X1)
                & v17_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v17_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
            <=> ( l3_lattices(k7_filter_1(X0,X1))
                & v17_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',t47_filter_1)).

fof(f302,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f301,f208])).

fof(f208,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f137])).

fof(f301,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f300,f207])).

fof(f207,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f137])).

fof(f300,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f299,f212])).

fof(f212,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f137])).

fof(f299,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f298,f211])).

fof(f211,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f137])).

fof(f298,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f206,f210])).

fof(f210,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f137])).

fof(f206,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f137])).

fof(f708,plain,(
    spl10_108 ),
    inference(avatar_split_clause,[],[f282,f706])).

fof(f706,plain,
    ( spl10_108
  <=> v15_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f282,plain,(
    v15_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ? [X0] :
      ( v15_lattices(X0)
      & v10_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & v4_lattices(X0)
      & v3_lattices(X0)
      & ~ v2_struct_0(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',rc11_lattices)).

fof(f701,plain,(
    spl10_106 ),
    inference(avatar_split_clause,[],[f281,f699])).

fof(f699,plain,
    ( spl10_106
  <=> v10_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f281,plain,(
    v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f694,plain,(
    spl10_104 ),
    inference(avatar_split_clause,[],[f280,f692])).

fof(f692,plain,
    ( spl10_104
  <=> v9_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f280,plain,(
    v9_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f687,plain,(
    spl10_102 ),
    inference(avatar_split_clause,[],[f279,f685])).

fof(f685,plain,
    ( spl10_102
  <=> v8_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f279,plain,(
    v8_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f680,plain,(
    spl10_100 ),
    inference(avatar_split_clause,[],[f278,f678])).

fof(f678,plain,
    ( spl10_100
  <=> v7_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f278,plain,(
    v7_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f673,plain,(
    spl10_98 ),
    inference(avatar_split_clause,[],[f277,f671])).

fof(f671,plain,
    ( spl10_98
  <=> v6_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f277,plain,(
    v6_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f666,plain,(
    spl10_96 ),
    inference(avatar_split_clause,[],[f276,f664])).

fof(f664,plain,
    ( spl10_96
  <=> v5_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f276,plain,(
    v5_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f659,plain,(
    spl10_94 ),
    inference(avatar_split_clause,[],[f275,f657])).

fof(f657,plain,
    ( spl10_94
  <=> v4_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f275,plain,(
    v4_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f652,plain,(
    spl10_92 ),
    inference(avatar_split_clause,[],[f274,f650])).

fof(f650,plain,
    ( spl10_92
  <=> v3_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f274,plain,(
    v3_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f645,plain,(
    ~ spl10_91 ),
    inference(avatar_split_clause,[],[f273,f643])).

fof(f273,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f638,plain,(
    spl10_88 ),
    inference(avatar_split_clause,[],[f272,f636])).

fof(f272,plain,(
    l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f631,plain,(
    spl10_86 ),
    inference(avatar_split_clause,[],[f271,f629])).

fof(f629,plain,
    ( spl10_86
  <=> v3_filter_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f271,plain,(
    v3_filter_0(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,axiom,(
    ? [X0] :
      ( v3_filter_0(X0)
      & v10_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & v4_lattices(X0)
      & v3_lattices(X0)
      & ~ v2_struct_0(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',rc1_filter_0)).

fof(f624,plain,(
    spl10_84 ),
    inference(avatar_split_clause,[],[f270,f622])).

fof(f622,plain,
    ( spl10_84
  <=> v10_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f270,plain,(
    v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f617,plain,(
    spl10_82 ),
    inference(avatar_split_clause,[],[f269,f615])).

fof(f615,plain,
    ( spl10_82
  <=> v9_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f269,plain,(
    v9_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f610,plain,(
    spl10_80 ),
    inference(avatar_split_clause,[],[f268,f608])).

fof(f608,plain,
    ( spl10_80
  <=> v8_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f268,plain,(
    v8_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f603,plain,(
    spl10_78 ),
    inference(avatar_split_clause,[],[f267,f601])).

fof(f601,plain,
    ( spl10_78
  <=> v7_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f267,plain,(
    v7_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f596,plain,(
    spl10_76 ),
    inference(avatar_split_clause,[],[f266,f594])).

fof(f594,plain,
    ( spl10_76
  <=> v6_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f266,plain,(
    v6_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f589,plain,(
    spl10_74 ),
    inference(avatar_split_clause,[],[f265,f587])).

fof(f587,plain,
    ( spl10_74
  <=> v5_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f265,plain,(
    v5_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f582,plain,(
    spl10_72 ),
    inference(avatar_split_clause,[],[f264,f580])).

fof(f580,plain,
    ( spl10_72
  <=> v4_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f264,plain,(
    v4_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f575,plain,(
    spl10_70 ),
    inference(avatar_split_clause,[],[f263,f573])).

fof(f573,plain,
    ( spl10_70
  <=> v3_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f263,plain,(
    v3_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f568,plain,(
    ~ spl10_69 ),
    inference(avatar_split_clause,[],[f262,f566])).

fof(f262,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f561,plain,(
    spl10_66 ),
    inference(avatar_split_clause,[],[f261,f559])).

fof(f261,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f103])).

fof(f554,plain,(
    spl10_64 ),
    inference(avatar_split_clause,[],[f260,f552])).

fof(f260,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',existence_l3_lattices)).

fof(f547,plain,(
    spl10_62 ),
    inference(avatar_split_clause,[],[f259,f545])).

fof(f545,plain,
    ( spl10_62
  <=> v3_lattices(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f259,plain,(
    v3_lattices(sK5) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,axiom,(
    ? [X0] :
      ( v3_lattices(X0)
      & ~ v2_struct_0(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',rc6_lattices)).

fof(f540,plain,(
    ~ spl10_61 ),
    inference(avatar_split_clause,[],[f258,f538])).

fof(f258,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f121])).

fof(f533,plain,(
    spl10_58 ),
    inference(avatar_split_clause,[],[f257,f531])).

fof(f257,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f121])).

fof(f526,plain,(
    spl10_56 ),
    inference(avatar_split_clause,[],[f256,f524])).

fof(f524,plain,
    ( spl10_56
  <=> v10_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f256,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,axiom,(
    ? [X0] :
      ( v10_lattices(X0)
      & v3_lattices(X0)
      & ~ v2_struct_0(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',rc9_lattices)).

fof(f519,plain,(
    spl10_54 ),
    inference(avatar_split_clause,[],[f255,f517])).

fof(f517,plain,
    ( spl10_54
  <=> v3_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f255,plain,(
    v3_lattices(sK4) ),
    inference(cnf_transformation,[],[f123])).

fof(f512,plain,(
    ~ spl10_53 ),
    inference(avatar_split_clause,[],[f254,f510])).

fof(f254,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f123])).

fof(f505,plain,(
    spl10_50 ),
    inference(avatar_split_clause,[],[f253,f503])).

fof(f253,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f123])).

fof(f498,plain,(
    spl10_48 ),
    inference(avatar_split_clause,[],[f252,f496])).

fof(f496,plain,
    ( spl10_48
  <=> v3_lattices(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f252,plain,(
    v3_lattices(sK3) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,axiom,(
    ? [X0] :
      ( v3_lattices(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',rc3_lattices)).

fof(f491,plain,(
    spl10_46 ),
    inference(avatar_split_clause,[],[f251,f489])).

fof(f251,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f114])).

fof(f484,plain,(
    spl10_44 ),
    inference(avatar_split_clause,[],[f245,f482])).

fof(f482,plain,
    ( spl10_44
  <=> v17_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f245,plain,(
    v17_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,axiom,(
    ? [X0] :
      ( v17_lattices(X0)
      & v10_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & v4_lattices(X0)
      & v3_lattices(X0)
      & ~ v2_struct_0(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t47_filter_1.p',rc13_lattices)).

fof(f477,plain,(
    spl10_42 ),
    inference(avatar_split_clause,[],[f244,f475])).

fof(f475,plain,
    ( spl10_42
  <=> v10_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f244,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f470,plain,(
    spl10_40 ),
    inference(avatar_split_clause,[],[f243,f468])).

fof(f468,plain,
    ( spl10_40
  <=> v9_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f243,plain,(
    v9_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f463,plain,(
    spl10_38 ),
    inference(avatar_split_clause,[],[f242,f461])).

fof(f461,plain,
    ( spl10_38
  <=> v8_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f242,plain,(
    v8_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f456,plain,(
    spl10_36 ),
    inference(avatar_split_clause,[],[f241,f454])).

fof(f454,plain,
    ( spl10_36
  <=> v7_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f241,plain,(
    v7_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f449,plain,(
    spl10_34 ),
    inference(avatar_split_clause,[],[f240,f447])).

fof(f447,plain,
    ( spl10_34
  <=> v6_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f240,plain,(
    v6_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f442,plain,(
    spl10_32 ),
    inference(avatar_split_clause,[],[f239,f440])).

fof(f440,plain,
    ( spl10_32
  <=> v5_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f239,plain,(
    v5_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f435,plain,(
    spl10_30 ),
    inference(avatar_split_clause,[],[f238,f433])).

fof(f433,plain,
    ( spl10_30
  <=> v4_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f238,plain,(
    v4_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f428,plain,(
    spl10_28 ),
    inference(avatar_split_clause,[],[f237,f426])).

fof(f426,plain,
    ( spl10_28
  <=> v3_lattices(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f237,plain,(
    v3_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f421,plain,(
    ~ spl10_27 ),
    inference(avatar_split_clause,[],[f236,f419])).

fof(f236,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f414,plain,(
    spl10_24 ),
    inference(avatar_split_clause,[],[f235,f412])).

fof(f235,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f407,plain,
    ( spl10_22
    | spl10_20 ),
    inference(avatar_split_clause,[],[f197,f395,f402])).

fof(f197,plain,
    ( l3_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f137])).

fof(f406,plain,
    ( spl10_22
    | spl10_18 ),
    inference(avatar_split_clause,[],[f196,f388,f402])).

fof(f196,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f137])).

fof(f405,plain,
    ( spl10_22
    | spl10_16 ),
    inference(avatar_split_clause,[],[f195,f381,f402])).

fof(f381,plain,
    ( spl10_16
  <=> v10_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f195,plain,
    ( v10_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f137])).

fof(f404,plain,
    ( spl10_22
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f194,f374,f402])).

fof(f194,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f137])).

fof(f397,plain,
    ( spl10_12
    | spl10_20 ),
    inference(avatar_split_clause,[],[f181,f395,f368])).

fof(f181,plain,
    ( l3_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f137])).

fof(f390,plain,
    ( spl10_12
    | spl10_18 ),
    inference(avatar_split_clause,[],[f180,f388,f368])).

fof(f180,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f137])).

fof(f383,plain,
    ( spl10_12
    | spl10_16 ),
    inference(avatar_split_clause,[],[f179,f381,f368])).

fof(f179,plain,
    ( v10_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f137])).

fof(f376,plain,
    ( spl10_12
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f178,f374,f368])).

fof(f178,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f137])).

fof(f363,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f212,f361])).

fof(f356,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f211,f354])).

fof(f349,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f210,f347])).

fof(f342,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f209,f340])).

fof(f335,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f208,f333])).

fof(f328,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f207,f326])).
%------------------------------------------------------------------------------
