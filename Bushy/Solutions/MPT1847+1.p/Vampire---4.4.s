%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t14_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:28 EDT 2019

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  748 (1932 expanded)
%              Number of leaves         :  195 ( 854 expanded)
%              Depth                    :   11
%              Number of atoms          : 2119 (5077 expanded)
%              Number of equality atoms :  188 ( 621 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1991,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f324,f331,f338,f345,f352,f359,f366,f373,f380,f387,f394,f401,f408,f415,f422,f429,f436,f443,f450,f457,f464,f471,f478,f485,f492,f499,f506,f513,f520,f527,f534,f541,f548,f561,f568,f575,f582,f589,f596,f605,f614,f641,f649,f657,f665,f715,f726,f755,f786,f794,f803,f813,f830,f838,f846,f854,f870,f872,f889,f1121,f1129,f1140,f1148,f1156,f1164,f1215,f1238,f1262,f1284,f1336,f1355,f1368,f1369,f1379,f1389,f1399,f1422,f1432,f1442,f1452,f1462,f1466,f1491,f1504,f1519,f1532,f1545,f1558,f1565,f1603,f1610,f1617,f1624,f1631,f1638,f1645,f1652,f1659,f1670,f1672,f1681,f1690,f1693,f1696,f1704,f1712,f1715,f1723,f1732,f1735,f1744,f1753,f1762,f1764,f1766,f1767,f1768,f1769,f1771,f1772,f1774,f1775,f1776,f1777,f1778,f1780,f1782,f1785,f1787,f1793,f1804,f1812,f1823,f1832,f1841,f1852,f1861,f1863,f1873,f1884,f1892,f1894,f1911,f1915,f1919,f1923,f1927,f1939,f1958,f1966,f1974,f1980,f1990])).

fof(f1990,plain,
    ( ~ spl33_0
    | ~ spl33_2
    | ~ spl33_6
    | spl33_209
    | ~ spl33_210 ),
    inference(avatar_contradiction_clause,[],[f1989])).

fof(f1989,plain,
    ( $false
    | ~ spl33_0
    | ~ spl33_2
    | ~ spl33_6
    | ~ spl33_209
    | ~ spl33_210 ),
    inference(subsumption_resolution,[],[f1988,f344])).

fof(f344,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ spl33_6 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl33_6
  <=> v1_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_6])])).

fof(f1988,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ spl33_0
    | ~ spl33_2
    | ~ spl33_209
    | ~ spl33_210 ),
    inference(subsumption_resolution,[],[f1987,f1616])).

fof(f1616,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl33_209 ),
    inference(avatar_component_clause,[],[f1615])).

fof(f1615,plain,
    ( spl33_209
  <=> ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_209])])).

fof(f1987,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0)
    | ~ spl33_0
    | ~ spl33_2
    | ~ spl33_210 ),
    inference(subsumption_resolution,[],[f1986,f323])).

fof(f323,plain,
    ( l1_pre_topc(sK0)
    | ~ spl33_0 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl33_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_0])])).

fof(f1986,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0)
    | ~ spl33_2
    | ~ spl33_210 ),
    inference(subsumption_resolution,[],[f1981,f330])).

fof(f330,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl33_2 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl33_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_2])])).

fof(f1981,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0)
    | ~ spl33_210 ),
    inference(resolution,[],[f1623,f317])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f121])).

fof(f121,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',d3_tex_2)).

fof(f1623,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl33_210 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f1622,plain,
    ( spl33_210
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_210])])).

fof(f1980,plain,
    ( spl33_210
    | ~ spl33_0
    | spl33_5
    | ~ spl33_10
    | ~ spl33_206 ),
    inference(avatar_split_clause,[],[f1979,f1608,f357,f336,f322,f1622])).

fof(f336,plain,
    ( spl33_5
  <=> ~ v1_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_5])])).

fof(f357,plain,
    ( spl33_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_10])])).

fof(f1608,plain,
    ( spl33_206
  <=> u1_struct_0(sK1) = sK3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_206])])).

fof(f1979,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl33_0
    | ~ spl33_5
    | ~ spl33_10
    | ~ spl33_206 ),
    inference(subsumption_resolution,[],[f1978,f337])).

fof(f337,plain,
    ( ~ v1_tex_2(sK2,sK0)
    | ~ spl33_5 ),
    inference(avatar_component_clause,[],[f336])).

fof(f1978,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0)
    | ~ spl33_0
    | ~ spl33_10
    | ~ spl33_206 ),
    inference(subsumption_resolution,[],[f1977,f323])).

fof(f1977,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(sK2,sK0)
    | ~ spl33_10
    | ~ spl33_206 ),
    inference(subsumption_resolution,[],[f1975,f358])).

fof(f358,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl33_10 ),
    inference(avatar_component_clause,[],[f357])).

fof(f1975,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(sK2,sK0)
    | ~ spl33_206 ),
    inference(superposition,[],[f204,f1609])).

fof(f1609,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK2)
    | ~ spl33_206 ),
    inference(avatar_component_clause,[],[f1608])).

fof(f204,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f1974,plain,
    ( ~ spl33_279
    | spl33_199
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1967,f1563,f1547,f1972])).

fof(f1972,plain,
    ( spl33_279
  <=> u1_struct_0(sK1) != u1_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_279])])).

fof(f1547,plain,
    ( spl33_199
  <=> u1_struct_0(sK2) != u1_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_199])])).

fof(f1563,plain,
    ( spl33_202
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_202])])).

fof(f1967,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK22)
    | ~ spl33_199
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1548,f1564])).

fof(f1564,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl33_202 ),
    inference(avatar_component_clause,[],[f1563])).

fof(f1548,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK22)
    | ~ spl33_199 ),
    inference(avatar_component_clause,[],[f1547])).

fof(f1966,plain,
    ( ~ spl33_277
    | spl33_195
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1959,f1563,f1534,f1964])).

fof(f1964,plain,
    ( spl33_277
  <=> u1_struct_0(sK1) != u1_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_277])])).

fof(f1534,plain,
    ( spl33_195
  <=> u1_struct_0(sK2) != u1_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_195])])).

fof(f1959,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK21)
    | ~ spl33_195
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1535,f1564])).

fof(f1535,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK21)
    | ~ spl33_195 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f1958,plain,
    ( ~ spl33_275
    | spl33_191
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1951,f1563,f1521,f1956])).

fof(f1956,plain,
    ( spl33_275
  <=> u1_struct_0(sK1) != u1_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_275])])).

fof(f1521,plain,
    ( spl33_191
  <=> u1_struct_0(sK2) != u1_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_191])])).

fof(f1951,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK20)
    | ~ spl33_191
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1522,f1564])).

fof(f1522,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK20)
    | ~ spl33_191 ),
    inference(avatar_component_clause,[],[f1521])).

fof(f1939,plain,
    ( ~ spl33_273
    | ~ spl33_202
    | spl33_245 ),
    inference(avatar_split_clause,[],[f1932,f1807,f1563,f1937])).

fof(f1937,plain,
    ( spl33_273
  <=> u1_struct_0(sK1) != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_273])])).

fof(f1807,plain,
    ( spl33_245
  <=> u1_struct_0(sK2) != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_245])])).

fof(f1932,plain,
    ( u1_struct_0(sK1) != sK17
    | ~ spl33_202
    | ~ spl33_245 ),
    inference(superposition,[],[f1808,f1564])).

fof(f1808,plain,
    ( u1_struct_0(sK2) != sK17
    | ~ spl33_245 ),
    inference(avatar_component_clause,[],[f1807])).

fof(f1927,plain,
    ( ~ spl33_177
    | spl33_270
    | ~ spl33_130 ),
    inference(avatar_split_clause,[],[f1899,f1162,f1925,f1457])).

fof(f1457,plain,
    ( spl33_177
  <=> ~ m1_subset_1(u1_pre_topc(sK22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK22)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_177])])).

fof(f1925,plain,
    ( spl33_270
  <=> ! [X9,X8] :
        ( g1_pre_topc(X8,X9) != sK22
        | u1_pre_topc(sK22) = X9 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_270])])).

fof(f1162,plain,
    ( spl33_130
  <=> g1_pre_topc(u1_struct_0(sK22),u1_pre_topc(sK22)) = sK22 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_130])])).

fof(f1899,plain,
    ( ! [X8,X9] :
        ( g1_pre_topc(X8,X9) != sK22
        | ~ m1_subset_1(u1_pre_topc(sK22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK22))))
        | u1_pre_topc(sK22) = X9 )
    | ~ spl33_130 ),
    inference(superposition,[],[f211,f1163])).

fof(f1163,plain,
    ( g1_pre_topc(u1_struct_0(sK22),u1_pre_topc(sK22)) = sK22
    | ~ spl33_130 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f211,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',free_g1_pre_topc)).

fof(f1923,plain,
    ( ~ spl33_173
    | spl33_268
    | ~ spl33_128 ),
    inference(avatar_split_clause,[],[f1898,f1154,f1921,f1447])).

fof(f1447,plain,
    ( spl33_173
  <=> ~ m1_subset_1(u1_pre_topc(sK21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK21)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_173])])).

fof(f1921,plain,
    ( spl33_268
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK21
        | u1_pre_topc(sK21) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_268])])).

fof(f1154,plain,
    ( spl33_128
  <=> g1_pre_topc(u1_struct_0(sK21),u1_pre_topc(sK21)) = sK21 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_128])])).

fof(f1898,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK21
        | ~ m1_subset_1(u1_pre_topc(sK21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK21))))
        | u1_pre_topc(sK21) = X7 )
    | ~ spl33_128 ),
    inference(superposition,[],[f211,f1155])).

fof(f1155,plain,
    ( g1_pre_topc(u1_struct_0(sK21),u1_pre_topc(sK21)) = sK21
    | ~ spl33_128 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1919,plain,
    ( ~ spl33_169
    | spl33_266
    | ~ spl33_126 ),
    inference(avatar_split_clause,[],[f1897,f1146,f1917,f1437])).

fof(f1437,plain,
    ( spl33_169
  <=> ~ m1_subset_1(u1_pre_topc(sK20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK20)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_169])])).

fof(f1917,plain,
    ( spl33_266
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK20
        | u1_pre_topc(sK20) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_266])])).

fof(f1146,plain,
    ( spl33_126
  <=> g1_pre_topc(u1_struct_0(sK20),u1_pre_topc(sK20)) = sK20 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_126])])).

fof(f1897,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK20
        | ~ m1_subset_1(u1_pre_topc(sK20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK20))))
        | u1_pre_topc(sK20) = X5 )
    | ~ spl33_126 ),
    inference(superposition,[],[f211,f1147])).

fof(f1147,plain,
    ( g1_pre_topc(u1_struct_0(sK20),u1_pre_topc(sK20)) = sK20
    | ~ spl33_126 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f1915,plain,
    ( ~ spl33_217
    | spl33_264
    | ~ spl33_204 ),
    inference(avatar_split_clause,[],[f1896,f1601,f1913,f1640])).

fof(f1640,plain,
    ( spl33_217
  <=> ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_217])])).

fof(f1913,plain,
    ( spl33_264
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_pre_topc(sK2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_264])])).

fof(f1601,plain,
    ( spl33_204
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_204])])).

fof(f1896,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | u1_pre_topc(sK2) = X3 )
    | ~ spl33_204 ),
    inference(superposition,[],[f211,f1602])).

fof(f1602,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | ~ spl33_204 ),
    inference(avatar_component_clause,[],[f1601])).

fof(f1911,plain,
    ( ~ spl33_161
    | spl33_262
    | ~ spl33_120 ),
    inference(avatar_split_clause,[],[f1895,f1119,f1909,f1417])).

fof(f1417,plain,
    ( spl33_161
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_161])])).

fof(f1909,plain,
    ( spl33_262
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_262])])).

fof(f1119,plain,
    ( spl33_120
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_120])])).

fof(f1895,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X1 )
    | ~ spl33_120 ),
    inference(superposition,[],[f211,f1120])).

fof(f1120,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl33_120 ),
    inference(avatar_component_clause,[],[f1119])).

fof(f1894,plain,
    ( ~ spl33_215
    | spl33_151
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1893,f1563,f1357,f1636])).

fof(f1636,plain,
    ( spl33_215
  <=> ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_215])])).

fof(f1357,plain,
    ( spl33_151
  <=> ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_151])])).

fof(f1893,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | ~ spl33_151
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1358,f1564])).

fof(f1358,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2))
    | ~ spl33_151 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f1892,plain,
    ( spl33_260
    | ~ spl33_86
    | ~ spl33_214 ),
    inference(avatar_split_clause,[],[f1885,f1633,f655,f1890])).

fof(f1890,plain,
    ( spl33_260
  <=> v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_260])])).

fof(f655,plain,
    ( spl33_86
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_86])])).

fof(f1633,plain,
    ( spl33_214
  <=> v1_zfmisc_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_214])])).

fof(f1885,plain,
    ( v7_struct_0(sK1)
    | ~ spl33_86
    | ~ spl33_214 ),
    inference(subsumption_resolution,[],[f1875,f656])).

fof(f656,plain,
    ( l1_struct_0(sK1)
    | ~ spl33_86 ),
    inference(avatar_component_clause,[],[f655])).

fof(f1875,plain,
    ( ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl33_214 ),
    inference(resolution,[],[f1634,f314])).

fof(f314,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f192,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f191])).

fof(f191,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f70,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',fc6_struct_0)).

fof(f1634,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | ~ spl33_214 ),
    inference(avatar_component_clause,[],[f1633])).

fof(f1884,plain,
    ( spl33_258
    | ~ spl33_86
    | ~ spl33_214
    | spl33_257 ),
    inference(avatar_split_clause,[],[f1877,f1871,f1633,f655,f1882])).

fof(f1882,plain,
    ( spl33_258
  <=> v1_zfmisc_1(sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_258])])).

fof(f1871,plain,
    ( spl33_257
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_257])])).

fof(f1877,plain,
    ( v1_zfmisc_1(sK5(sK1))
    | ~ spl33_86
    | ~ spl33_214
    | ~ spl33_257 ),
    inference(subsumption_resolution,[],[f1876,f656])).

fof(f1876,plain,
    ( ~ l1_struct_0(sK1)
    | v1_zfmisc_1(sK5(sK1))
    | ~ spl33_214
    | ~ spl33_257 ),
    inference(subsumption_resolution,[],[f1874,f1872])).

fof(f1872,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl33_257 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f1874,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v1_zfmisc_1(sK5(sK1))
    | ~ spl33_214 ),
    inference(resolution,[],[f1634,f988])).

fof(f988,plain,(
    ! [X1] :
      ( ~ v1_zfmisc_1(u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v1_zfmisc_1(sK5(X1)) ) ),
    inference(resolution,[],[f222,f283])).

fof(f283,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',cc5_funct_1)).

fof(f222,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f137])).

fof(f137,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f102])).

fof(f102,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc4_struct_0)).

fof(f1873,plain,
    ( ~ spl33_257
    | ~ spl33_86
    | spl33_213 ),
    inference(avatar_split_clause,[],[f1866,f1629,f655,f1871])).

fof(f1629,plain,
    ( spl33_213
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_213])])).

fof(f1866,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl33_86
    | ~ spl33_213 ),
    inference(subsumption_resolution,[],[f1865,f656])).

fof(f1865,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl33_213 ),
    inference(resolution,[],[f1630,f218])).

fof(f218,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f133])).

fof(f133,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',fc1_struct_0)).

fof(f1630,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl33_213 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f1863,plain,
    ( ~ spl33_213
    | spl33_147
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1862,f1563,f1347,f1629])).

fof(f1347,plain,
    ( spl33_147
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_147])])).

fof(f1862,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl33_147
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1348,f1564])).

fof(f1348,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl33_147 ),
    inference(avatar_component_clause,[],[f1347])).

fof(f1861,plain,
    ( spl33_254
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1854,f1563,f862,f663,f371,f1859])).

fof(f1859,plain,
    ( spl33_254
  <=> sK14(k1_zfmisc_1(sK10(u1_struct_0(sK1)))) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_254])])).

fof(f371,plain,
    ( spl33_14
  <=> v1_xboole_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_14])])).

fof(f663,plain,
    ( spl33_88
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_88])])).

fof(f862,plain,
    ( spl33_112
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_112])])).

fof(f1854,plain,
    ( sK14(k1_zfmisc_1(sK10(u1_struct_0(sK1)))) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1853,f1564])).

fof(f1853,plain,
    ( sK14(k1_zfmisc_1(sK10(u1_struct_0(sK2)))) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f1802,f664])).

fof(f664,plain,
    ( l1_struct_0(sK2)
    | ~ spl33_88 ),
    inference(avatar_component_clause,[],[f663])).

fof(f1802,plain,
    ( ~ l1_struct_0(sK2)
    | sK14(k1_zfmisc_1(sK10(u1_struct_0(sK2)))) = sK17
    | ~ spl33_14
    | ~ spl33_112 ),
    inference(resolution,[],[f863,f899])).

fof(f899,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | sK14(k1_zfmisc_1(sK10(u1_struct_0(X0)))) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f746,f218])).

fof(f746,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK14(k1_zfmisc_1(sK10(X1))) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f702,f692])).

fof(f692,plain,(
    ! [X0] :
      ( v1_xboole_0(sK10(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f257,f234])).

fof(f234,plain,(
    ! [X0] : m1_subset_1(sK10(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc3_subset_1)).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f167])).

fof(f167,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',cc1_subset_1)).

fof(f702,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK14(k1_zfmisc_1(X0)) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f694,f615])).

fof(f615,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK17 = X0 )
    | ~ spl33_14 ),
    inference(resolution,[],[f207,f372])).

fof(f372,plain,
    ( v1_xboole_0(sK17)
    | ~ spl33_14 ),
    inference(avatar_component_clause,[],[f371])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f118])).

fof(f118,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',t8_boole)).

fof(f694,plain,(
    ! [X2] :
      ( v1_xboole_0(sK14(k1_zfmisc_1(X2)))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f257,f254])).

fof(f254,plain,(
    ! [X0] : m1_subset_1(sK14(X0),X0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',existence_m1_subset_1)).

fof(f863,plain,
    ( v2_struct_0(sK2)
    | ~ spl33_112 ),
    inference(avatar_component_clause,[],[f862])).

fof(f1852,plain,
    ( spl33_252
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1845,f1563,f862,f663,f371,f1850])).

fof(f1850,plain,
    ( spl33_252
  <=> sK10(sK14(k1_zfmisc_1(u1_struct_0(sK1)))) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_252])])).

fof(f1845,plain,
    ( sK10(sK14(k1_zfmisc_1(u1_struct_0(sK1)))) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1844,f1564])).

fof(f1844,plain,
    ( sK10(sK14(k1_zfmisc_1(u1_struct_0(sK2)))) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f1801,f664])).

fof(f1801,plain,
    ( ~ l1_struct_0(sK2)
    | sK10(sK14(k1_zfmisc_1(u1_struct_0(sK2)))) = sK17
    | ~ spl33_14
    | ~ spl33_112 ),
    inference(resolution,[],[f863,f894])).

fof(f894,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | sK10(sK14(k1_zfmisc_1(u1_struct_0(X0)))) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f707,f218])).

fof(f707,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK10(sK14(k1_zfmisc_1(X2))) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f699,f694])).

fof(f699,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(X0) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f692,f615])).

fof(f1841,plain,
    ( spl33_250
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1834,f1563,f862,f663,f371,f1839])).

fof(f1839,plain,
    ( spl33_250
  <=> sK10(sK10(u1_struct_0(sK1))) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_250])])).

fof(f1834,plain,
    ( sK10(sK10(u1_struct_0(sK1))) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1833,f1564])).

fof(f1833,plain,
    ( sK10(sK10(u1_struct_0(sK2))) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f1799,f664])).

fof(f1799,plain,
    ( ~ l1_struct_0(sK2)
    | sK10(sK10(u1_struct_0(sK2))) = sK17
    | ~ spl33_14
    | ~ spl33_112 ),
    inference(resolution,[],[f863,f762])).

fof(f762,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | sK10(sK10(u1_struct_0(X0))) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f706,f218])).

fof(f706,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK10(sK10(X1)) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f699,f692])).

fof(f1832,plain,
    ( spl33_248
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1825,f1563,f862,f663,f371,f1830])).

fof(f1830,plain,
    ( spl33_248
  <=> sK14(k1_zfmisc_1(u1_struct_0(sK1))) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_248])])).

fof(f1825,plain,
    ( sK14(k1_zfmisc_1(u1_struct_0(sK1))) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1824,f1564])).

fof(f1824,plain,
    ( sK14(k1_zfmisc_1(u1_struct_0(sK2))) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f1798,f664])).

fof(f1798,plain,
    ( ~ l1_struct_0(sK2)
    | sK14(k1_zfmisc_1(u1_struct_0(sK2))) = sK17
    | ~ spl33_14
    | ~ spl33_112 ),
    inference(resolution,[],[f863,f745])).

fof(f745,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | sK14(k1_zfmisc_1(u1_struct_0(X0))) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f702,f218])).

fof(f1823,plain,
    ( spl33_246
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1816,f1563,f862,f663,f371,f1821])).

fof(f1821,plain,
    ( spl33_246
  <=> sK10(u1_struct_0(sK1)) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_246])])).

fof(f1816,plain,
    ( sK10(u1_struct_0(sK1)) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1815,f1564])).

fof(f1815,plain,
    ( sK10(u1_struct_0(sK2)) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f1797,f664])).

fof(f1797,plain,
    ( ~ l1_struct_0(sK2)
    | sK10(u1_struct_0(sK2)) = sK17
    | ~ spl33_14
    | ~ spl33_112 ),
    inference(resolution,[],[f863,f705])).

fof(f705,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | sK10(u1_struct_0(X0)) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f699,f218])).

fof(f1812,plain,
    ( spl33_244
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(avatar_split_clause,[],[f1805,f862,f663,f371,f1810])).

fof(f1810,plain,
    ( spl33_244
  <=> u1_struct_0(sK2) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_244])])).

fof(f1805,plain,
    ( u1_struct_0(sK2) = sK17
    | ~ spl33_14
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f1795,f664])).

fof(f1795,plain,
    ( ~ l1_struct_0(sK2)
    | u1_struct_0(sK2) = sK17
    | ~ spl33_14
    | ~ spl33_112 ),
    inference(resolution,[],[f863,f623])).

fof(f623,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | u1_struct_0(X0) = sK17 )
    | ~ spl33_14 ),
    inference(resolution,[],[f218,f615])).

fof(f1804,plain,
    ( spl33_156
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(avatar_split_clause,[],[f1803,f862,f663,f1384])).

fof(f1384,plain,
    ( spl33_156
  <=> v7_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_156])])).

fof(f1803,plain,
    ( v7_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f1794,f664])).

fof(f1794,plain,
    ( ~ l1_struct_0(sK2)
    | v7_struct_0(sK2)
    | ~ spl33_112 ),
    inference(resolution,[],[f863,f315])).

fof(f315,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f194,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f193])).

fof(f193,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
       => v7_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',cc1_struct_0)).

fof(f1793,plain,
    ( ~ spl33_217
    | spl33_242
    | ~ spl33_204 ),
    inference(avatar_split_clause,[],[f1789,f1601,f1791,f1640])).

fof(f1791,plain,
    ( spl33_242
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(sK1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_242])])).

fof(f1789,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | u1_struct_0(sK1) = X2 )
    | ~ spl33_204 ),
    inference(superposition,[],[f210,f1602])).

fof(f210,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f126])).

fof(f1787,plain,
    ( spl33_212
    | ~ spl33_146
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1786,f1563,f1344,f1626])).

fof(f1626,plain,
    ( spl33_212
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_212])])).

fof(f1344,plain,
    ( spl33_146
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_146])])).

fof(f1786,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl33_146
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1345,f1564])).

fof(f1345,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl33_146 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1785,plain,
    ( spl33_212
    | ~ spl33_223
    | ~ spl33_164
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1784,f1563,f1424,f1668,f1626])).

fof(f1668,plain,
    ( spl33_223
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_223])])).

fof(f1424,plain,
    ( spl33_164
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_164])])).

fof(f1784,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl33_164
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1783,f1564])).

fof(f1783,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl33_164
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1467,f1564])).

fof(f1467,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl33_164 ),
    inference(resolution,[],[f1425,f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | ~ v2_struct_0(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & ~ v1_xboole_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',fc9_pre_topc)).

fof(f1425,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl33_164 ),
    inference(avatar_component_clause,[],[f1424])).

fof(f1782,plain,
    ( spl33_214
    | ~ spl33_150
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1781,f1563,f1360,f1633])).

fof(f1360,plain,
    ( spl33_150
  <=> v1_zfmisc_1(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_150])])).

fof(f1781,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | ~ spl33_150
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1361,f1564])).

fof(f1361,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2))
    | ~ spl33_150 ),
    inference(avatar_component_clause,[],[f1360])).

fof(f1780,plain,
    ( ~ spl33_157
    | spl33_214
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1779,f1563,f663,f1633,f1387])).

fof(f1387,plain,
    ( spl33_157
  <=> ~ v7_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_157])])).

fof(f1779,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | ~ v7_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1584,f664])).

fof(f1584,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | ~ v7_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f297,f1564])).

fof(f297,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f175])).

fof(f175,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',fc7_struct_0)).

fof(f1778,plain,
    ( spl33_156
    | ~ spl33_215
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1694,f1563,f663,f1636,f1384])).

fof(f1694,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | v7_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1585,f664])).

fof(f1585,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v7_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f314,f1564])).

fof(f1777,plain,
    ( spl33_156
    | spl33_236
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1736,f1563,f663,f1742,f1384])).

fof(f1742,plain,
    ( spl33_236
  <=> v1_subset_1(sK30(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_236])])).

fof(f1736,plain,
    ( v1_subset_1(sK30(sK2),u1_struct_0(sK1))
    | v7_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1594,f664])).

fof(f1594,plain,
    ( v1_subset_1(sK30(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v7_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f1264,f1564])).

fof(f1264,plain,(
    ! [X0] :
      ( v1_subset_1(sK30(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f303,f315])).

fof(f303,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_subset_1(sK30(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc6_tex_2)).

fof(f1776,plain,
    ( spl33_156
    | spl33_238
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1745,f1563,f663,f1751,f1384])).

fof(f1751,plain,
    ( spl33_238
  <=> v1_subset_1(sK31(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_238])])).

fof(f1745,plain,
    ( v1_subset_1(sK31(sK2),u1_struct_0(sK1))
    | v7_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1595,f664])).

fof(f1595,plain,
    ( v1_subset_1(sK31(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v7_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f1266,f1564])).

fof(f1266,plain,(
    ! [X0] :
      ( v1_subset_1(sK31(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f307,f315])).

fof(f307,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_subset_1(sK31(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f184,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f183])).

fof(f183,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f104])).

fof(f104,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc4_tex_2)).

fof(f1775,plain,
    ( spl33_156
    | ~ spl33_241
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1754,f1563,f663,f1760,f1384])).

fof(f1760,plain,
    ( spl33_241
  <=> ~ v1_subset_1(sK32(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_241])])).

fof(f1754,plain,
    ( ~ v1_subset_1(sK32(sK2),u1_struct_0(sK1))
    | v7_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1596,f664])).

fof(f1596,plain,
    ( ~ v1_subset_1(sK32(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v7_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f1268,f1564])).

fof(f1268,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK32(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f311,f315])).

fof(f311,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_subset_1(sK32(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f185])).

fof(f185,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f106,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc5_tex_2)).

fof(f1774,plain,
    ( ~ spl33_113
    | ~ spl33_88
    | spl33_147 ),
    inference(avatar_split_clause,[],[f1773,f1347,f663,f859])).

fof(f859,plain,
    ( spl33_113
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_113])])).

fof(f1773,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_147 ),
    inference(subsumption_resolution,[],[f1370,f664])).

fof(f1370,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v2_struct_0(sK2)
    | ~ spl33_147 ),
    inference(resolution,[],[f1348,f218])).

fof(f1772,plain,
    ( spl33_112
    | ~ spl33_223
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1662,f1563,f647,f1668,f862])).

fof(f647,plain,
    ( spl33_84
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_84])])).

fof(f1662,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | v2_struct_0(sK2)
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1578,f648])).

fof(f648,plain,
    ( l1_pre_topc(sK2)
    | ~ spl33_84 ),
    inference(avatar_component_clause,[],[f647])).

fof(f1578,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f214,f1564])).

fof(f214,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',fc7_pre_topc)).

fof(f1771,plain,
    ( ~ spl33_113
    | spl33_212
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1770,f1563,f663,f1626,f859])).

fof(f1770,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1580,f664])).

fof(f1580,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | ~ v2_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f218,f1564])).

fof(f1769,plain,
    ( spl33_112
    | spl33_224
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1673,f1563,f663,f1679,f862])).

fof(f1679,plain,
    ( spl33_224
  <=> m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_224])])).

fof(f1673,plain,
    ( m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1581,f664])).

fof(f1581,plain,
    ( m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f219,f1564])).

fof(f219,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f136])).

fof(f136,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f87])).

fof(f87,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc20_struct_0)).

fof(f1768,plain,
    ( spl33_112
    | spl33_226
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1682,f1563,f663,f1688,f862])).

fof(f1688,plain,
    ( spl33_226
  <=> m1_subset_1(sK5(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_226])])).

fof(f1682,plain,
    ( m1_subset_1(sK5(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1582,f664])).

fof(f1582,plain,
    ( m1_subset_1(sK5(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f222,f1564])).

fof(f1767,plain,
    ( spl33_112
    | ~ spl33_213
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1691,f1563,f663,f1629,f862])).

fof(f1691,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1583,f664])).

fof(f1583,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f224,f1564])).

fof(f224,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',fc2_struct_0)).

fof(f1766,plain,
    ( ~ spl33_113
    | spl33_214
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1765,f1563,f663,f1633,f859])).

fof(f1765,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | ~ v2_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1586,f664])).

fof(f1586,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | ~ v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f625,f1564])).

fof(f625,plain,(
    ! [X3] :
      ( v1_zfmisc_1(u1_struct_0(X3))
      | ~ v2_struct_0(X3)
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f218,f281])).

fof(f281,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f169,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',cc1_zfmisc_1)).

fof(f1764,plain,
    ( spl33_234
    | spl33_112
    | ~ spl33_215
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1763,f1563,f663,f1636,f862,f1730])).

fof(f1730,plain,
    ( spl33_234
  <=> v1_zfmisc_1(sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_234])])).

fof(f1763,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | v1_zfmisc_1(sK5(sK2))
    | ~ spl33_88
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1591,f664])).

fof(f1591,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_zfmisc_1(sK5(sK2))
    | ~ spl33_202 ),
    inference(superposition,[],[f988,f1564])).

fof(f1762,plain,
    ( ~ spl33_241
    | ~ spl33_88
    | spl33_157
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1755,f1563,f1387,f663,f1760])).

fof(f1755,plain,
    ( ~ v1_subset_1(sK32(sK2),u1_struct_0(sK1))
    | ~ spl33_88
    | ~ spl33_157
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1754,f1388])).

fof(f1388,plain,
    ( ~ v7_struct_0(sK2)
    | ~ spl33_157 ),
    inference(avatar_component_clause,[],[f1387])).

fof(f1753,plain,
    ( spl33_238
    | ~ spl33_88
    | spl33_157
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1746,f1563,f1387,f663,f1751])).

fof(f1746,plain,
    ( v1_subset_1(sK31(sK2),u1_struct_0(sK1))
    | ~ spl33_88
    | ~ spl33_157
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1745,f1388])).

fof(f1744,plain,
    ( spl33_236
    | ~ spl33_88
    | spl33_157
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1737,f1563,f1387,f663,f1742])).

fof(f1737,plain,
    ( v1_subset_1(sK30(sK2),u1_struct_0(sK1))
    | ~ spl33_88
    | ~ spl33_157
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1736,f1388])).

fof(f1735,plain,
    ( ~ spl33_223
    | spl33_212
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1734,f1563,f647,f1626,f1668])).

fof(f1734,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(forward_demodulation,[],[f1733,f1564])).

fof(f1733,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1592,f648])).

fof(f1592,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f994,f1564])).

fof(f994,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f208,f217])).

fof(f217,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f132])).

fof(f132,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',dt_u1_pre_topc)).

fof(f1732,plain,
    ( spl33_234
    | ~ spl33_215
    | ~ spl33_88
    | spl33_113
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1725,f1563,f859,f663,f1636,f1730])).

fof(f1725,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | v1_zfmisc_1(sK5(sK2))
    | ~ spl33_88
    | ~ spl33_113
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1724,f664])).

fof(f1724,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v1_zfmisc_1(sK5(sK2))
    | ~ spl33_113
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1591,f860])).

fof(f860,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl33_113 ),
    inference(avatar_component_clause,[],[f859])).

fof(f1723,plain,
    ( spl33_232
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1716,f1563,f647,f1721])).

fof(f1721,plain,
    ( spl33_232
  <=> l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_232])])).

fof(f1716,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1590,f648])).

fof(f1590,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f777,f1564])).

fof(f777,plain,(
    ! [X0] :
      ( l1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f756,f233])).

fof(f233,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',dt_l1_pre_topc)).

fof(f756,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f217,f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',dt_g1_pre_topc)).

fof(f1715,plain,
    ( ~ spl33_221
    | ~ spl33_84
    | spl33_185
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1714,f1563,f1493,f647,f1657])).

fof(f1657,plain,
    ( spl33_221
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_221])])).

fof(f1493,plain,
    ( spl33_185
  <=> ~ v1_zfmisc_1(u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_185])])).

fof(f1714,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl33_84
    | ~ spl33_185
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1713,f648])).

fof(f1713,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_185
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1589,f1494])).

fof(f1494,plain,
    ( ~ v1_zfmisc_1(u1_pre_topc(sK2))
    | ~ spl33_185 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f1589,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f767,f1564])).

fof(f767,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f283,f217])).

fof(f1712,plain,
    ( spl33_230
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1705,f1563,f647,f1710])).

fof(f1710,plain,
    ( spl33_230
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_230])])).

fof(f1705,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1588,f648])).

fof(f1588,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f757,f1564])).

fof(f757,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f217,f212])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f1704,plain,
    ( spl33_228
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1697,f1563,f647,f1702])).

fof(f1702,plain,
    ( spl33_228
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_228])])).

fof(f1697,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1587,f648])).

fof(f1587,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f756,f1564])).

fof(f1696,plain,
    ( ~ spl33_215
    | ~ spl33_88
    | spl33_157
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1695,f1563,f1387,f663,f1636])).

fof(f1695,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | ~ spl33_88
    | ~ spl33_157
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1694,f1388])).

fof(f1693,plain,
    ( ~ spl33_213
    | ~ spl33_88
    | spl33_113
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1692,f1563,f859,f663,f1629])).

fof(f1692,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl33_88
    | ~ spl33_113
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1691,f860])).

fof(f1690,plain,
    ( spl33_226
    | ~ spl33_88
    | spl33_113
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1683,f1563,f859,f663,f1688])).

fof(f1683,plain,
    ( m1_subset_1(sK5(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl33_88
    | ~ spl33_113
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1682,f860])).

fof(f1681,plain,
    ( spl33_224
    | ~ spl33_88
    | spl33_113
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1674,f1563,f859,f663,f1679])).

fof(f1674,plain,
    ( m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl33_88
    | ~ spl33_113
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1673,f860])).

fof(f1672,plain,
    ( spl33_216
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1671,f1563,f647,f1643])).

fof(f1643,plain,
    ( spl33_216
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_216])])).

fof(f1671,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl33_84
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1579,f648])).

fof(f1579,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_202 ),
    inference(superposition,[],[f217,f1564])).

fof(f1670,plain,
    ( ~ spl33_223
    | ~ spl33_84
    | spl33_113
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1663,f1563,f859,f647,f1668])).

fof(f1663,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ spl33_84
    | ~ spl33_113
    | ~ spl33_202 ),
    inference(subsumption_resolution,[],[f1662,f860])).

fof(f1659,plain,
    ( ~ spl33_221
    | spl33_187
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1575,f1563,f1502,f1657])).

fof(f1502,plain,
    ( spl33_187
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_187])])).

fof(f1575,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl33_187
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f1503])).

fof(f1503,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl33_187 ),
    inference(avatar_component_clause,[],[f1502])).

fof(f1652,plain,
    ( ~ spl33_219
    | spl33_183
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1574,f1563,f1486,f1650])).

fof(f1650,plain,
    ( spl33_219
  <=> ~ v1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_219])])).

fof(f1486,plain,
    ( spl33_183
  <=> ~ v1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_183])])).

fof(f1574,plain,
    ( ~ v1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl33_183
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f1487])).

fof(f1487,plain,
    ( ~ v1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl33_183 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f1645,plain,
    ( spl33_216
    | ~ spl33_164
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1572,f1563,f1424,f1643])).

fof(f1572,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl33_164
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f1425])).

fof(f1638,plain,
    ( ~ spl33_215
    | spl33_151
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1571,f1563,f1357,f1636])).

fof(f1571,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | ~ spl33_151
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f1358])).

fof(f1631,plain,
    ( ~ spl33_213
    | spl33_147
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1570,f1563,f1347,f1629])).

fof(f1570,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl33_147
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f1348])).

fof(f1624,plain,
    ( spl33_210
    | ~ spl33_144
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1569,f1563,f1334,f1622])).

fof(f1334,plain,
    ( spl33_144
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_144])])).

fof(f1569,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl33_144
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f1335])).

fof(f1335,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl33_144 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1617,plain,
    ( ~ spl33_209
    | spl33_143
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1568,f1563,f1282,f1615])).

fof(f1282,plain,
    ( spl33_143
  <=> ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_143])])).

fof(f1568,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl33_143
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f1283])).

fof(f1283,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl33_143 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f1610,plain,
    ( spl33_206
    | ~ spl33_136
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1567,f1563,f1236,f1608])).

fof(f1236,plain,
    ( spl33_136
  <=> u1_struct_0(sK2) = sK3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_136])])).

fof(f1567,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK2)
    | ~ spl33_136
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f1237])).

fof(f1237,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ spl33_136 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f1603,plain,
    ( spl33_204
    | ~ spl33_8
    | ~ spl33_202 ),
    inference(avatar_split_clause,[],[f1566,f1563,f350,f1601])).

fof(f350,plain,
    ( spl33_8
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_8])])).

fof(f1566,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | ~ spl33_8
    | ~ spl33_202 ),
    inference(backward_demodulation,[],[f1564,f351])).

fof(f351,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl33_8 ),
    inference(avatar_component_clause,[],[f350])).

fof(f1565,plain,
    ( spl33_202
    | ~ spl33_166 ),
    inference(avatar_split_clause,[],[f1511,f1430,f1563])).

fof(f1430,plain,
    ( spl33_166
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(sK2) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_166])])).

fof(f1511,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl33_166 ),
    inference(equality_resolution,[],[f1431])).

fof(f1431,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(sK2) = X2 )
    | ~ spl33_166 ),
    inference(avatar_component_clause,[],[f1430])).

fof(f1558,plain,
    ( spl33_198
    | ~ spl33_201
    | ~ spl33_130
    | ~ spl33_166 ),
    inference(avatar_split_clause,[],[f1510,f1430,f1162,f1556,f1550])).

fof(f1550,plain,
    ( spl33_198
  <=> u1_struct_0(sK2) = u1_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_198])])).

fof(f1556,plain,
    ( spl33_201
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK22 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_201])])).

fof(f1510,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK22
    | u1_struct_0(sK2) = u1_struct_0(sK22)
    | ~ spl33_130
    | ~ spl33_166 ),
    inference(superposition,[],[f1431,f1163])).

fof(f1545,plain,
    ( spl33_194
    | ~ spl33_197
    | ~ spl33_128
    | ~ spl33_166 ),
    inference(avatar_split_clause,[],[f1509,f1430,f1154,f1543,f1537])).

fof(f1537,plain,
    ( spl33_194
  <=> u1_struct_0(sK2) = u1_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_194])])).

fof(f1543,plain,
    ( spl33_197
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK21 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_197])])).

fof(f1509,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK21
    | u1_struct_0(sK2) = u1_struct_0(sK21)
    | ~ spl33_128
    | ~ spl33_166 ),
    inference(superposition,[],[f1431,f1155])).

fof(f1532,plain,
    ( spl33_190
    | ~ spl33_193
    | ~ spl33_126
    | ~ spl33_166 ),
    inference(avatar_split_clause,[],[f1508,f1430,f1146,f1530,f1524])).

fof(f1524,plain,
    ( spl33_190
  <=> u1_struct_0(sK2) = u1_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_190])])).

fof(f1530,plain,
    ( spl33_193
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK20 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_193])])).

fof(f1508,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK20
    | u1_struct_0(sK2) = u1_struct_0(sK20)
    | ~ spl33_126
    | ~ spl33_166 ),
    inference(superposition,[],[f1431,f1147])).

fof(f1519,plain,
    ( spl33_188
    | ~ spl33_120
    | ~ spl33_166 ),
    inference(avatar_split_clause,[],[f1512,f1430,f1119,f1517])).

fof(f1517,plain,
    ( spl33_188
  <=> u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_188])])).

fof(f1512,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl33_120
    | ~ spl33_166 ),
    inference(trivial_inequality_removal,[],[f1506])).

fof(f1506,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl33_120
    | ~ spl33_166 ),
    inference(superposition,[],[f1431,f1120])).

fof(f1504,plain,
    ( spl33_184
    | ~ spl33_187
    | ~ spl33_164 ),
    inference(avatar_split_clause,[],[f1472,f1424,f1502,f1496])).

fof(f1496,plain,
    ( spl33_184
  <=> v1_zfmisc_1(u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_184])])).

fof(f1472,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(u1_pre_topc(sK2))
    | ~ spl33_164 ),
    inference(resolution,[],[f1425,f283])).

fof(f1491,plain,
    ( ~ spl33_181
    | spl33_182
    | ~ spl33_164 ),
    inference(avatar_split_clause,[],[f1478,f1424,f1489,f1483])).

fof(f1483,plain,
    ( spl33_181
  <=> ~ v1_xboole_0(u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_181])])).

fof(f1489,plain,
    ( spl33_182
  <=> v1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_182])])).

fof(f1478,plain,
    ( v1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_pre_topc(sK2))
    | ~ spl33_164 ),
    inference(subsumption_resolution,[],[f1470,f260])).

fof(f260,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',fc1_subset_1)).

fof(f1470,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_pre_topc(sK2))
    | ~ spl33_164 ),
    inference(resolution,[],[f1425,f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f163])).

fof(f163,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',cc2_subset_1)).

fof(f1466,plain,
    ( ~ spl33_84
    | spl33_165 ),
    inference(avatar_contradiction_clause,[],[f1465])).

fof(f1465,plain,
    ( $false
    | ~ spl33_84
    | ~ spl33_165 ),
    inference(subsumption_resolution,[],[f1464,f648])).

fof(f1464,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl33_165 ),
    inference(resolution,[],[f1428,f217])).

fof(f1428,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl33_165 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f1427,plain,
    ( spl33_165
  <=> ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_165])])).

fof(f1462,plain,
    ( ~ spl33_177
    | spl33_178
    | ~ spl33_130 ),
    inference(avatar_split_clause,[],[f1404,f1162,f1460,f1457])).

fof(f1460,plain,
    ( spl33_178
  <=> ! [X9,X8] :
        ( g1_pre_topc(X8,X9) != sK22
        | u1_struct_0(sK22) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_178])])).

fof(f1404,plain,
    ( ! [X8,X9] :
        ( g1_pre_topc(X8,X9) != sK22
        | ~ m1_subset_1(u1_pre_topc(sK22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK22))))
        | u1_struct_0(sK22) = X8 )
    | ~ spl33_130 ),
    inference(superposition,[],[f210,f1163])).

fof(f1452,plain,
    ( ~ spl33_173
    | spl33_174
    | ~ spl33_128 ),
    inference(avatar_split_clause,[],[f1403,f1154,f1450,f1447])).

fof(f1450,plain,
    ( spl33_174
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK21
        | u1_struct_0(sK21) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_174])])).

fof(f1403,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK21
        | ~ m1_subset_1(u1_pre_topc(sK21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK21))))
        | u1_struct_0(sK21) = X6 )
    | ~ spl33_128 ),
    inference(superposition,[],[f210,f1155])).

fof(f1442,plain,
    ( ~ spl33_169
    | spl33_170
    | ~ spl33_126 ),
    inference(avatar_split_clause,[],[f1402,f1146,f1440,f1437])).

fof(f1440,plain,
    ( spl33_170
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK20
        | u1_struct_0(sK20) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_170])])).

fof(f1402,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK20
        | ~ m1_subset_1(u1_pre_topc(sK20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK20))))
        | u1_struct_0(sK20) = X4 )
    | ~ spl33_126 ),
    inference(superposition,[],[f210,f1147])).

fof(f1432,plain,
    ( ~ spl33_165
    | spl33_166
    | ~ spl33_8 ),
    inference(avatar_split_clause,[],[f1401,f350,f1430,f1427])).

fof(f1401,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | u1_struct_0(sK2) = X2 )
    | ~ spl33_8 ),
    inference(superposition,[],[f210,f351])).

fof(f1422,plain,
    ( ~ spl33_161
    | spl33_162
    | ~ spl33_120 ),
    inference(avatar_split_clause,[],[f1400,f1119,f1420,f1417])).

fof(f1420,plain,
    ( spl33_162
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_162])])).

fof(f1400,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0 )
    | ~ spl33_120 ),
    inference(superposition,[],[f210,f1120])).

fof(f1399,plain,
    ( ~ spl33_159
    | ~ spl33_66
    | spl33_153 ),
    inference(avatar_split_clause,[],[f1392,f1366,f559,f1397])).

fof(f1397,plain,
    ( spl33_159
  <=> ~ v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_159])])).

fof(f559,plain,
    ( spl33_66
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_66])])).

fof(f1366,plain,
    ( spl33_153
  <=> ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_153])])).

fof(f1392,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl33_66
    | ~ spl33_153 ),
    inference(subsumption_resolution,[],[f1391,f560])).

fof(f560,plain,
    ( l1_struct_0(sK0)
    | ~ spl33_66 ),
    inference(avatar_component_clause,[],[f559])).

fof(f1391,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl33_153 ),
    inference(resolution,[],[f1367,f297])).

fof(f1367,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl33_153 ),
    inference(avatar_component_clause,[],[f1366])).

fof(f1389,plain,
    ( ~ spl33_157
    | ~ spl33_88
    | spl33_151 ),
    inference(avatar_split_clause,[],[f1382,f1357,f663,f1387])).

fof(f1382,plain,
    ( ~ v7_struct_0(sK2)
    | ~ spl33_88
    | ~ spl33_151 ),
    inference(subsumption_resolution,[],[f1381,f664])).

fof(f1381,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v7_struct_0(sK2)
    | ~ spl33_151 ),
    inference(resolution,[],[f1358,f297])).

fof(f1379,plain,
    ( ~ spl33_155
    | ~ spl33_66
    | spl33_149 ),
    inference(avatar_split_clause,[],[f1372,f1350,f559,f1377])).

fof(f1377,plain,
    ( spl33_155
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_155])])).

fof(f1350,plain,
    ( spl33_149
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_149])])).

fof(f1372,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl33_66
    | ~ spl33_149 ),
    inference(subsumption_resolution,[],[f1371,f560])).

fof(f1371,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl33_149 ),
    inference(resolution,[],[f1351,f218])).

fof(f1351,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl33_149 ),
    inference(avatar_component_clause,[],[f1350])).

fof(f1369,plain,
    ( spl33_146
    | ~ spl33_149
    | ~ spl33_144 ),
    inference(avatar_split_clause,[],[f1341,f1334,f1350,f1344])).

fof(f1341,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl33_144 ),
    inference(resolution,[],[f1335,f257])).

fof(f1368,plain,
    ( spl33_150
    | ~ spl33_153
    | ~ spl33_144 ),
    inference(avatar_split_clause,[],[f1340,f1334,f1366,f1360])).

fof(f1340,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | ~ spl33_144 ),
    inference(resolution,[],[f1335,f283])).

fof(f1355,plain,
    ( ~ spl33_147
    | spl33_148
    | spl33_143
    | ~ spl33_144 ),
    inference(avatar_split_clause,[],[f1342,f1334,f1282,f1353,f1347])).

fof(f1353,plain,
    ( spl33_148
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_148])])).

fof(f1342,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl33_143
    | ~ spl33_144 ),
    inference(subsumption_resolution,[],[f1338,f1283])).

fof(f1338,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl33_144 ),
    inference(resolution,[],[f1335,f252])).

fof(f1336,plain,
    ( spl33_144
    | ~ spl33_0
    | spl33_5
    | ~ spl33_10
    | ~ spl33_136 ),
    inference(avatar_split_clause,[],[f1329,f1236,f357,f336,f322,f1334])).

fof(f1329,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl33_0
    | ~ spl33_5
    | ~ spl33_10
    | ~ spl33_136 ),
    inference(subsumption_resolution,[],[f1328,f337])).

fof(f1328,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0)
    | ~ spl33_0
    | ~ spl33_10
    | ~ spl33_136 ),
    inference(subsumption_resolution,[],[f1327,f323])).

fof(f1327,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(sK2,sK0)
    | ~ spl33_10
    | ~ spl33_136 ),
    inference(subsumption_resolution,[],[f1324,f358])).

fof(f1324,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(sK2,sK0)
    | ~ spl33_136 ),
    inference(superposition,[],[f204,f1237])).

fof(f1284,plain,
    ( ~ spl33_143
    | ~ spl33_0
    | spl33_5
    | ~ spl33_10
    | ~ spl33_136 ),
    inference(avatar_split_clause,[],[f1277,f1236,f357,f336,f322,f1282])).

fof(f1277,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl33_0
    | ~ spl33_5
    | ~ spl33_10
    | ~ spl33_136 ),
    inference(subsumption_resolution,[],[f1276,f337])).

fof(f1276,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0)
    | ~ spl33_0
    | ~ spl33_10
    | ~ spl33_136 ),
    inference(subsumption_resolution,[],[f1275,f323])).

fof(f1275,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(sK2,sK0)
    | ~ spl33_10
    | ~ spl33_136 ),
    inference(subsumption_resolution,[],[f1273,f358])).

fof(f1273,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(sK2,sK0)
    | ~ spl33_136 ),
    inference(superposition,[],[f206,f1237])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f1262,plain,
    ( spl33_138
    | ~ spl33_141
    | ~ spl33_26
    | ~ spl33_126 ),
    inference(avatar_split_clause,[],[f1249,f1146,f413,f1260,f1254])).

fof(f1254,plain,
    ( spl33_138
  <=> v1_xboole_0(u1_struct_0(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_138])])).

fof(f1260,plain,
    ( spl33_141
  <=> ~ v2_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_141])])).

fof(f413,plain,
    ( spl33_26
  <=> l1_pre_topc(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_26])])).

fof(f1249,plain,
    ( ~ v2_struct_0(sK20)
    | v1_xboole_0(u1_struct_0(sK20))
    | ~ spl33_26
    | ~ spl33_126 ),
    inference(subsumption_resolution,[],[f1242,f414])).

fof(f414,plain,
    ( l1_pre_topc(sK20)
    | ~ spl33_26 ),
    inference(avatar_component_clause,[],[f413])).

fof(f1242,plain,
    ( ~ v2_struct_0(sK20)
    | v1_xboole_0(u1_struct_0(sK20))
    | ~ l1_pre_topc(sK20)
    | ~ spl33_126 ),
    inference(superposition,[],[f994,f1147])).

fof(f1238,plain,
    ( spl33_136
    | ~ spl33_0
    | spl33_5
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f1231,f357,f336,f322,f1236])).

fof(f1231,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ spl33_0
    | ~ spl33_5
    | ~ spl33_10 ),
    inference(subsumption_resolution,[],[f1230,f337])).

fof(f1230,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0)
    | ~ spl33_0
    | ~ spl33_10 ),
    inference(subsumption_resolution,[],[f1223,f323])).

fof(f1223,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0)
    | ~ spl33_10 ),
    inference(resolution,[],[f205,f358])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f1215,plain,
    ( ~ spl33_133
    | spl33_134
    | ~ spl33_104 ),
    inference(avatar_split_clause,[],[f1202,f828,f1213,f1207])).

fof(f1207,plain,
    ( spl33_133
  <=> ~ v1_xboole_0(u1_pre_topc(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_133])])).

fof(f1213,plain,
    ( spl33_134
  <=> v1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_134])])).

fof(f828,plain,
    ( spl33_104
  <=> m1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(k1_zfmisc_1(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_104])])).

fof(f1202,plain,
    ( v1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(sK17))
    | ~ v1_xboole_0(u1_pre_topc(sK19))
    | ~ spl33_104 ),
    inference(subsumption_resolution,[],[f1185,f260])).

fof(f1185,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK17))
    | v1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(sK17))
    | ~ v1_xboole_0(u1_pre_topc(sK19))
    | ~ spl33_104 ),
    inference(resolution,[],[f252,f829])).

fof(f829,plain,
    ( m1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(k1_zfmisc_1(sK17)))
    | ~ spl33_104 ),
    inference(avatar_component_clause,[],[f828])).

fof(f1164,plain,
    ( spl33_130
    | ~ spl33_36
    | ~ spl33_42 ),
    inference(avatar_split_clause,[],[f1157,f469,f448,f1162])).

fof(f448,plain,
    ( spl33_36
  <=> v1_pre_topc(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_36])])).

fof(f469,plain,
    ( spl33_42
  <=> l1_pre_topc(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_42])])).

fof(f1157,plain,
    ( g1_pre_topc(u1_struct_0(sK22),u1_pre_topc(sK22)) = sK22
    | ~ spl33_36
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f1103,f470])).

fof(f470,plain,
    ( l1_pre_topc(sK22)
    | ~ spl33_42 ),
    inference(avatar_component_clause,[],[f469])).

fof(f1103,plain,
    ( ~ l1_pre_topc(sK22)
    | g1_pre_topc(u1_struct_0(sK22),u1_pre_topc(sK22)) = sK22
    | ~ spl33_36 ),
    inference(resolution,[],[f216,f449])).

fof(f449,plain,
    ( v1_pre_topc(sK22)
    | ~ spl33_36 ),
    inference(avatar_component_clause,[],[f448])).

fof(f216,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f130])).

fof(f130,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',abstractness_v1_pre_topc)).

fof(f1156,plain,
    ( spl33_128
    | ~ spl33_28
    | ~ spl33_34 ),
    inference(avatar_split_clause,[],[f1149,f441,f420,f1154])).

fof(f420,plain,
    ( spl33_28
  <=> v1_pre_topc(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_28])])).

fof(f441,plain,
    ( spl33_34
  <=> l1_pre_topc(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_34])])).

fof(f1149,plain,
    ( g1_pre_topc(u1_struct_0(sK21),u1_pre_topc(sK21)) = sK21
    | ~ spl33_28
    | ~ spl33_34 ),
    inference(subsumption_resolution,[],[f1102,f442])).

fof(f442,plain,
    ( l1_pre_topc(sK21)
    | ~ spl33_34 ),
    inference(avatar_component_clause,[],[f441])).

fof(f1102,plain,
    ( ~ l1_pre_topc(sK21)
    | g1_pre_topc(u1_struct_0(sK21),u1_pre_topc(sK21)) = sK21
    | ~ spl33_28 ),
    inference(resolution,[],[f216,f421])).

fof(f421,plain,
    ( v1_pre_topc(sK21)
    | ~ spl33_28 ),
    inference(avatar_component_clause,[],[f420])).

fof(f1148,plain,
    ( spl33_126
    | ~ spl33_24
    | ~ spl33_26 ),
    inference(avatar_split_clause,[],[f1141,f413,f406,f1146])).

fof(f406,plain,
    ( spl33_24
  <=> v1_pre_topc(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_24])])).

fof(f1141,plain,
    ( g1_pre_topc(u1_struct_0(sK20),u1_pre_topc(sK20)) = sK20
    | ~ spl33_24
    | ~ spl33_26 ),
    inference(subsumption_resolution,[],[f1101,f414])).

fof(f1101,plain,
    ( ~ l1_pre_topc(sK20)
    | g1_pre_topc(u1_struct_0(sK20),u1_pre_topc(sK20)) = sK20
    | ~ spl33_24 ),
    inference(resolution,[],[f216,f407])).

fof(f407,plain,
    ( v1_pre_topc(sK20)
    | ~ spl33_24 ),
    inference(avatar_component_clause,[],[f406])).

fof(f1140,plain,
    ( spl33_124
    | ~ spl33_18
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(avatar_split_clause,[],[f1133,f811,f399,f385,f1138])).

fof(f1138,plain,
    ( spl33_124
  <=> g1_pre_topc(sK17,u1_pre_topc(sK19)) = sK19 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_124])])).

fof(f385,plain,
    ( spl33_18
  <=> v1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_18])])).

fof(f399,plain,
    ( spl33_22
  <=> l1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_22])])).

fof(f811,plain,
    ( spl33_102
  <=> u1_struct_0(sK19) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_102])])).

fof(f1133,plain,
    ( g1_pre_topc(sK17,u1_pre_topc(sK19)) = sK19
    | ~ spl33_18
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(forward_demodulation,[],[f1132,f812])).

fof(f812,plain,
    ( u1_struct_0(sK19) = sK17
    | ~ spl33_102 ),
    inference(avatar_component_clause,[],[f811])).

fof(f1132,plain,
    ( g1_pre_topc(u1_struct_0(sK19),u1_pre_topc(sK19)) = sK19
    | ~ spl33_18
    | ~ spl33_22 ),
    inference(subsumption_resolution,[],[f1100,f400])).

fof(f400,plain,
    ( l1_pre_topc(sK19)
    | ~ spl33_22 ),
    inference(avatar_component_clause,[],[f399])).

fof(f1100,plain,
    ( ~ l1_pre_topc(sK19)
    | g1_pre_topc(u1_struct_0(sK19),u1_pre_topc(sK19)) = sK19
    | ~ spl33_18 ),
    inference(resolution,[],[f216,f386])).

fof(f386,plain,
    ( v1_pre_topc(sK19)
    | ~ spl33_18 ),
    inference(avatar_component_clause,[],[f385])).

fof(f1129,plain,
    ( spl33_122
    | ~ spl33_106
    | ~ spl33_108 ),
    inference(avatar_split_clause,[],[f1122,f844,f836,f1127])).

fof(f1127,plain,
    ( spl33_122
  <=> g1_pre_topc(sK17,u1_pre_topc(sK19)) = g1_pre_topc(u1_struct_0(g1_pre_topc(sK17,u1_pre_topc(sK19))),u1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_122])])).

fof(f836,plain,
    ( spl33_106
  <=> l1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_106])])).

fof(f844,plain,
    ( spl33_108
  <=> v1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_108])])).

fof(f1122,plain,
    ( g1_pre_topc(sK17,u1_pre_topc(sK19)) = g1_pre_topc(u1_struct_0(g1_pre_topc(sK17,u1_pre_topc(sK19))),u1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19))))
    | ~ spl33_106
    | ~ spl33_108 ),
    inference(subsumption_resolution,[],[f1097,f837])).

fof(f837,plain,
    ( l1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ spl33_106 ),
    inference(avatar_component_clause,[],[f836])).

fof(f1097,plain,
    ( ~ l1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | g1_pre_topc(sK17,u1_pre_topc(sK19)) = g1_pre_topc(u1_struct_0(g1_pre_topc(sK17,u1_pre_topc(sK19))),u1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19))))
    | ~ spl33_108 ),
    inference(resolution,[],[f216,f845])).

fof(f845,plain,
    ( v1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ spl33_108 ),
    inference(avatar_component_clause,[],[f844])).

fof(f1121,plain,
    ( spl33_120
    | ~ spl33_96
    | ~ spl33_100 ),
    inference(avatar_split_clause,[],[f1114,f801,f784,f1119])).

fof(f784,plain,
    ( spl33_96
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_96])])).

fof(f801,plain,
    ( spl33_100
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_100])])).

fof(f1114,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl33_96
    | ~ spl33_100 ),
    inference(subsumption_resolution,[],[f1096,f785])).

fof(f785,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl33_96 ),
    inference(avatar_component_clause,[],[f784])).

fof(f1096,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl33_100 ),
    inference(resolution,[],[f216,f802])).

fof(f802,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl33_100 ),
    inference(avatar_component_clause,[],[f801])).

fof(f889,plain,
    ( spl33_116
    | ~ spl33_119
    | ~ spl33_104 ),
    inference(avatar_split_clause,[],[f875,f828,f887,f881])).

fof(f881,plain,
    ( spl33_116
  <=> v1_zfmisc_1(u1_pre_topc(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_116])])).

fof(f887,plain,
    ( spl33_119
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_119])])).

fof(f875,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(sK17))
    | v1_zfmisc_1(u1_pre_topc(sK19))
    | ~ spl33_104 ),
    inference(resolution,[],[f829,f283])).

fof(f872,plain,
    ( spl33_110
    | ~ spl33_106 ),
    inference(avatar_split_clause,[],[f871,f836,f852])).

fof(f852,plain,
    ( spl33_110
  <=> l1_struct_0(g1_pre_topc(sK17,u1_pre_topc(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_110])])).

fof(f871,plain,
    ( l1_struct_0(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ spl33_106 ),
    inference(resolution,[],[f837,f233])).

fof(f870,plain,
    ( spl33_112
    | ~ spl33_115
    | ~ spl33_8
    | ~ spl33_84 ),
    inference(avatar_split_clause,[],[f857,f647,f350,f868,f862])).

fof(f868,plain,
    ( spl33_115
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_115])])).

fof(f857,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v2_struct_0(sK2)
    | ~ spl33_8
    | ~ spl33_84 ),
    inference(subsumption_resolution,[],[f856,f648])).

fof(f856,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl33_8 ),
    inference(superposition,[],[f214,f351])).

fof(f854,plain,
    ( spl33_110
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(avatar_split_clause,[],[f847,f811,f399,f852])).

fof(f847,plain,
    ( l1_struct_0(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(subsumption_resolution,[],[f822,f400])).

fof(f822,plain,
    ( l1_struct_0(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ l1_pre_topc(sK19)
    | ~ spl33_102 ),
    inference(superposition,[],[f777,f812])).

fof(f846,plain,
    ( spl33_108
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(avatar_split_clause,[],[f839,f811,f399,f844])).

fof(f839,plain,
    ( v1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(subsumption_resolution,[],[f821,f400])).

fof(f821,plain,
    ( v1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ l1_pre_topc(sK19)
    | ~ spl33_102 ),
    inference(superposition,[],[f757,f812])).

fof(f838,plain,
    ( spl33_106
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(avatar_split_clause,[],[f831,f811,f399,f836])).

fof(f831,plain,
    ( l1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(subsumption_resolution,[],[f820,f400])).

fof(f820,plain,
    ( l1_pre_topc(g1_pre_topc(sK17,u1_pre_topc(sK19)))
    | ~ l1_pre_topc(sK19)
    | ~ spl33_102 ),
    inference(superposition,[],[f756,f812])).

fof(f830,plain,
    ( spl33_104
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(avatar_split_clause,[],[f823,f811,f399,f828])).

fof(f823,plain,
    ( m1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(k1_zfmisc_1(sK17)))
    | ~ spl33_22
    | ~ spl33_102 ),
    inference(subsumption_resolution,[],[f814,f400])).

fof(f814,plain,
    ( m1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(k1_zfmisc_1(sK17)))
    | ~ l1_pre_topc(sK19)
    | ~ spl33_102 ),
    inference(superposition,[],[f217,f812])).

fof(f813,plain,
    ( spl33_102
    | ~ spl33_14
    | ~ spl33_20
    | ~ spl33_70 ),
    inference(avatar_split_clause,[],[f806,f573,f392,f371,f811])).

fof(f392,plain,
    ( spl33_20
  <=> v2_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_20])])).

fof(f573,plain,
    ( spl33_70
  <=> l1_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_70])])).

fof(f806,plain,
    ( u1_struct_0(sK19) = sK17
    | ~ spl33_14
    | ~ spl33_20
    | ~ spl33_70 ),
    inference(subsumption_resolution,[],[f805,f574])).

fof(f574,plain,
    ( l1_struct_0(sK19)
    | ~ spl33_70 ),
    inference(avatar_component_clause,[],[f573])).

fof(f805,plain,
    ( ~ l1_struct_0(sK19)
    | u1_struct_0(sK19) = sK17
    | ~ spl33_14
    | ~ spl33_20 ),
    inference(resolution,[],[f623,f393])).

fof(f393,plain,
    ( v2_struct_0(sK19)
    | ~ spl33_20 ),
    inference(avatar_component_clause,[],[f392])).

fof(f803,plain,
    ( spl33_100
    | ~ spl33_8
    | ~ spl33_84 ),
    inference(avatar_split_clause,[],[f796,f647,f350,f801])).

fof(f796,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl33_8
    | ~ spl33_84 ),
    inference(subsumption_resolution,[],[f795,f648])).

fof(f795,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_8 ),
    inference(superposition,[],[f757,f351])).

fof(f794,plain,
    ( spl33_98
    | ~ spl33_96 ),
    inference(avatar_split_clause,[],[f787,f784,f792])).

fof(f792,plain,
    ( spl33_98
  <=> l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_98])])).

fof(f787,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl33_96 ),
    inference(resolution,[],[f785,f233])).

fof(f786,plain,
    ( spl33_96
    | ~ spl33_8
    | ~ spl33_84 ),
    inference(avatar_split_clause,[],[f779,f647,f350,f784])).

fof(f779,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl33_8
    | ~ spl33_84 ),
    inference(subsumption_resolution,[],[f778,f648])).

fof(f778,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ spl33_8 ),
    inference(superposition,[],[f756,f351])).

fof(f755,plain,
    ( spl33_94
    | ~ spl33_14 ),
    inference(avatar_split_clause,[],[f748,f371,f753])).

fof(f753,plain,
    ( spl33_94
  <=> sK14(k1_zfmisc_1(sK17)) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_94])])).

fof(f748,plain,
    ( sK14(k1_zfmisc_1(sK17)) = sK17
    | ~ spl33_14 ),
    inference(resolution,[],[f702,f372])).

fof(f726,plain,
    ( ~ spl33_93
    | ~ spl33_90 ),
    inference(avatar_split_clause,[],[f719,f713,f724])).

fof(f724,plain,
    ( spl33_93
  <=> ~ v1_subset_1(sK17,sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_93])])).

fof(f713,plain,
    ( spl33_90
  <=> sK10(sK17) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_90])])).

fof(f719,plain,
    ( ~ v1_subset_1(sK17,sK17)
    | ~ spl33_90 ),
    inference(superposition,[],[f235,f714])).

fof(f714,plain,
    ( sK10(sK17) = sK17
    | ~ spl33_90 ),
    inference(avatar_component_clause,[],[f713])).

fof(f235,plain,(
    ! [X0] : ~ v1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f98])).

fof(f715,plain,
    ( spl33_90
    | ~ spl33_14 ),
    inference(avatar_split_clause,[],[f708,f371,f713])).

fof(f708,plain,
    ( sK10(sK17) = sK17
    | ~ spl33_14 ),
    inference(resolution,[],[f699,f372])).

fof(f665,plain,
    ( spl33_88
    | ~ spl33_84 ),
    inference(avatar_split_clause,[],[f658,f647,f663])).

fof(f658,plain,
    ( l1_struct_0(sK2)
    | ~ spl33_84 ),
    inference(resolution,[],[f648,f233])).

fof(f657,plain,
    ( spl33_86
    | ~ spl33_82 ),
    inference(avatar_split_clause,[],[f650,f639,f655])).

fof(f639,plain,
    ( spl33_82
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_82])])).

fof(f650,plain,
    ( l1_struct_0(sK1)
    | ~ spl33_82 ),
    inference(resolution,[],[f640,f233])).

fof(f640,plain,
    ( l1_pre_topc(sK1)
    | ~ spl33_82 ),
    inference(avatar_component_clause,[],[f639])).

fof(f649,plain,
    ( spl33_84
    | ~ spl33_0
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f642,f357,f322,f647])).

fof(f642,plain,
    ( l1_pre_topc(sK2)
    | ~ spl33_0
    | ~ spl33_10 ),
    inference(subsumption_resolution,[],[f629,f323])).

fof(f629,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl33_10 ),
    inference(resolution,[],[f231,f358])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',dt_m1_pre_topc)).

fof(f641,plain,
    ( spl33_82
    | ~ spl33_0
    | ~ spl33_2 ),
    inference(avatar_split_clause,[],[f634,f329,f322,f639])).

fof(f634,plain,
    ( l1_pre_topc(sK1)
    | ~ spl33_0
    | ~ spl33_2 ),
    inference(subsumption_resolution,[],[f628,f323])).

fof(f628,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl33_2 ),
    inference(resolution,[],[f231,f330])).

fof(f614,plain,
    ( spl33_80
    | ~ spl33_20
    | ~ spl33_70 ),
    inference(avatar_split_clause,[],[f607,f573,f392,f612])).

fof(f612,plain,
    ( spl33_80
  <=> v7_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_80])])).

fof(f607,plain,
    ( v7_struct_0(sK19)
    | ~ spl33_20
    | ~ spl33_70 ),
    inference(subsumption_resolution,[],[f606,f574])).

fof(f606,plain,
    ( ~ l1_struct_0(sK19)
    | v7_struct_0(sK19)
    | ~ spl33_20 ),
    inference(resolution,[],[f315,f393])).

fof(f605,plain,
    ( spl33_78
    | ~ spl33_14 ),
    inference(avatar_split_clause,[],[f597,f371,f603])).

fof(f603,plain,
    ( spl33_78
  <=> v1_zfmisc_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_78])])).

fof(f597,plain,
    ( v1_zfmisc_1(sK17)
    | ~ spl33_14 ),
    inference(resolution,[],[f281,f372])).

fof(f596,plain,
    ( spl33_76
    | ~ spl33_42 ),
    inference(avatar_split_clause,[],[f554,f469,f594])).

fof(f594,plain,
    ( spl33_76
  <=> l1_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_76])])).

fof(f554,plain,
    ( l1_struct_0(sK22)
    | ~ spl33_42 ),
    inference(resolution,[],[f233,f470])).

fof(f589,plain,
    ( spl33_74
    | ~ spl33_34 ),
    inference(avatar_split_clause,[],[f553,f441,f587])).

fof(f587,plain,
    ( spl33_74
  <=> l1_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_74])])).

fof(f553,plain,
    ( l1_struct_0(sK21)
    | ~ spl33_34 ),
    inference(resolution,[],[f233,f442])).

fof(f582,plain,
    ( spl33_72
    | ~ spl33_26 ),
    inference(avatar_split_clause,[],[f552,f413,f580])).

fof(f580,plain,
    ( spl33_72
  <=> l1_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_72])])).

fof(f552,plain,
    ( l1_struct_0(sK20)
    | ~ spl33_26 ),
    inference(resolution,[],[f233,f414])).

fof(f575,plain,
    ( spl33_70
    | ~ spl33_22 ),
    inference(avatar_split_clause,[],[f551,f399,f573])).

fof(f551,plain,
    ( l1_struct_0(sK19)
    | ~ spl33_22 ),
    inference(resolution,[],[f233,f400])).

fof(f568,plain,
    ( spl33_68
    | ~ spl33_12 ),
    inference(avatar_split_clause,[],[f550,f364,f566])).

fof(f566,plain,
    ( spl33_68
  <=> l1_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_68])])).

fof(f364,plain,
    ( spl33_12
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_12])])).

fof(f550,plain,
    ( l1_struct_0(sK9)
    | ~ spl33_12 ),
    inference(resolution,[],[f233,f365])).

fof(f365,plain,
    ( l1_pre_topc(sK9)
    | ~ spl33_12 ),
    inference(avatar_component_clause,[],[f364])).

fof(f561,plain,
    ( spl33_66
    | ~ spl33_0 ),
    inference(avatar_split_clause,[],[f549,f322,f559])).

fof(f549,plain,
    ( l1_struct_0(sK0)
    | ~ spl33_0 ),
    inference(resolution,[],[f233,f323])).

fof(f548,plain,(
    spl33_64 ),
    inference(avatar_split_clause,[],[f294,f546])).

fof(f546,plain,
    ( spl33_64
  <=> l1_struct_0(sK29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_64])])).

fof(f294,plain,(
    l1_struct_0(sK29) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,axiom,(
    ? [X0] :
      ( ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc10_struct_0)).

fof(f541,plain,(
    ~ spl33_63 ),
    inference(avatar_split_clause,[],[f295,f539])).

fof(f539,plain,
    ( spl33_63
  <=> ~ v2_struct_0(sK29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_63])])).

fof(f295,plain,(
    ~ v2_struct_0(sK29) ),
    inference(cnf_transformation,[],[f77])).

fof(f534,plain,(
    ~ spl33_61 ),
    inference(avatar_split_clause,[],[f296,f532])).

fof(f532,plain,
    ( spl33_61
  <=> ~ v7_struct_0(sK29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_61])])).

fof(f296,plain,(
    ~ v7_struct_0(sK29) ),
    inference(cnf_transformation,[],[f77])).

fof(f527,plain,(
    spl33_58 ),
    inference(avatar_split_clause,[],[f291,f525])).

fof(f525,plain,
    ( spl33_58
  <=> l1_struct_0(sK28) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_58])])).

fof(f291,plain,(
    l1_struct_0(sK28) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ? [X0] :
      ( v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc9_struct_0)).

fof(f520,plain,(
    ~ spl33_57 ),
    inference(avatar_split_clause,[],[f292,f518])).

fof(f518,plain,
    ( spl33_57
  <=> ~ v2_struct_0(sK28) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_57])])).

fof(f292,plain,(
    ~ v2_struct_0(sK28) ),
    inference(cnf_transformation,[],[f110])).

fof(f513,plain,(
    spl33_54 ),
    inference(avatar_split_clause,[],[f293,f511])).

fof(f511,plain,
    ( spl33_54
  <=> v7_struct_0(sK28) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_54])])).

fof(f293,plain,(
    v7_struct_0(sK28) ),
    inference(cnf_transformation,[],[f110])).

fof(f506,plain,(
    ~ spl33_53 ),
    inference(avatar_split_clause,[],[f279,f504])).

fof(f504,plain,
    ( spl33_53
  <=> ~ v1_xboole_0(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_53])])).

fof(f279,plain,(
    ~ v1_xboole_0(sK25) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ? [X0] :
      ( ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc2_realset1)).

fof(f499,plain,(
    ~ spl33_51 ),
    inference(avatar_split_clause,[],[f280,f497])).

fof(f497,plain,
    ( spl33_51
  <=> ~ v1_zfmisc_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_51])])).

fof(f280,plain,(
    ~ v1_zfmisc_1(sK25) ),
    inference(cnf_transformation,[],[f89])).

fof(f492,plain,(
    ~ spl33_49 ),
    inference(avatar_split_clause,[],[f277,f490])).

fof(f490,plain,
    ( spl33_49
  <=> ~ v1_xboole_0(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_49])])).

fof(f277,plain,(
    ~ v1_xboole_0(sK24) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,axiom,(
    ? [X0] :
      ( v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc1_realset1)).

fof(f485,plain,(
    spl33_46 ),
    inference(avatar_split_clause,[],[f278,f483])).

fof(f483,plain,
    ( spl33_46
  <=> v1_zfmisc_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_46])])).

fof(f278,plain,(
    v1_zfmisc_1(sK24) ),
    inference(cnf_transformation,[],[f81])).

fof(f478,plain,(
    spl33_44 ),
    inference(avatar_split_clause,[],[f276,f476])).

fof(f476,plain,
    ( spl33_44
  <=> l1_struct_0(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_44])])).

fof(f276,plain,(
    l1_struct_0(sK23) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',existence_l1_struct_0)).

fof(f471,plain,(
    spl33_42 ),
    inference(avatar_split_clause,[],[f272,f469])).

fof(f272,plain,(
    l1_pre_topc(sK22) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc2_tex_1)).

fof(f464,plain,(
    ~ spl33_41 ),
    inference(avatar_split_clause,[],[f273,f462])).

fof(f462,plain,
    ( spl33_41
  <=> ~ v2_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_41])])).

fof(f273,plain,(
    ~ v2_struct_0(sK22) ),
    inference(cnf_transformation,[],[f92])).

fof(f457,plain,(
    ~ spl33_39 ),
    inference(avatar_split_clause,[],[f274,f455])).

fof(f455,plain,
    ( spl33_39
  <=> ~ v7_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_39])])).

fof(f274,plain,(
    ~ v7_struct_0(sK22) ),
    inference(cnf_transformation,[],[f92])).

fof(f450,plain,(
    spl33_36 ),
    inference(avatar_split_clause,[],[f275,f448])).

fof(f275,plain,(
    v1_pre_topc(sK22) ),
    inference(cnf_transformation,[],[f92])).

fof(f443,plain,(
    spl33_34 ),
    inference(avatar_split_clause,[],[f268,f441])).

fof(f268,plain,(
    l1_pre_topc(sK21) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc1_tex_1)).

fof(f436,plain,(
    ~ spl33_33 ),
    inference(avatar_split_clause,[],[f269,f434])).

fof(f434,plain,
    ( spl33_33
  <=> ~ v2_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_33])])).

fof(f269,plain,(
    ~ v2_struct_0(sK21) ),
    inference(cnf_transformation,[],[f84])).

fof(f429,plain,(
    spl33_30 ),
    inference(avatar_split_clause,[],[f270,f427])).

fof(f427,plain,
    ( spl33_30
  <=> v7_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_30])])).

fof(f270,plain,(
    v7_struct_0(sK21) ),
    inference(cnf_transformation,[],[f84])).

fof(f422,plain,(
    spl33_28 ),
    inference(avatar_split_clause,[],[f271,f420])).

fof(f271,plain,(
    v1_pre_topc(sK21) ),
    inference(cnf_transformation,[],[f84])).

fof(f415,plain,(
    spl33_26 ),
    inference(avatar_split_clause,[],[f266,f413])).

fof(f266,plain,(
    l1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc1_pre_topc)).

fof(f408,plain,(
    spl33_24 ),
    inference(avatar_split_clause,[],[f267,f406])).

fof(f267,plain,(
    v1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f80])).

fof(f401,plain,(
    spl33_22 ),
    inference(avatar_split_clause,[],[f263,f399])).

fof(f263,plain,(
    l1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc11_pre_topc)).

fof(f394,plain,(
    spl33_20 ),
    inference(avatar_split_clause,[],[f264,f392])).

fof(f264,plain,(
    v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f78])).

fof(f387,plain,(
    spl33_18 ),
    inference(avatar_split_clause,[],[f265,f385])).

fof(f265,plain,(
    v1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f78])).

fof(f380,plain,(
    ~ spl33_17 ),
    inference(avatar_split_clause,[],[f262,f378])).

fof(f378,plain,
    ( spl33_17
  <=> ~ v1_xboole_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_17])])).

fof(f262,plain,(
    ~ v1_xboole_0(sK18) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc2_xboole_0)).

fof(f373,plain,(
    spl33_14 ),
    inference(avatar_split_clause,[],[f261,f371])).

fof(f261,plain,(
    v1_xboole_0(sK17) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',rc1_xboole_0)).

fof(f366,plain,(
    spl33_12 ),
    inference(avatar_split_clause,[],[f232,f364])).

fof(f232,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',existence_l1_pre_topc)).

fof(f359,plain,(
    spl33_10 ),
    inference(avatar_split_clause,[],[f197,f357])).

fof(f197,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f119])).

fof(f119,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t14_tex_2.p',t14_tex_2)).

fof(f352,plain,(
    spl33_8 ),
    inference(avatar_split_clause,[],[f198,f350])).

fof(f198,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f120])).

fof(f345,plain,(
    spl33_6 ),
    inference(avatar_split_clause,[],[f199,f343])).

fof(f199,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f120])).

fof(f338,plain,(
    ~ spl33_5 ),
    inference(avatar_split_clause,[],[f200,f336])).

fof(f200,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f120])).

fof(f331,plain,(
    spl33_2 ),
    inference(avatar_split_clause,[],[f201,f329])).

fof(f201,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f120])).

fof(f324,plain,(
    spl33_0 ),
    inference(avatar_split_clause,[],[f202,f322])).

fof(f202,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f120])).
%------------------------------------------------------------------------------
