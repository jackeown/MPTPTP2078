%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t24_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:42 EDT 2019

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       : 1062 (4968 expanded)
%              Number of leaves         :  304 (2388 expanded)
%              Depth                    :    9
%              Number of atoms          : 3134 (13599 expanded)
%              Number of equality atoms :  165 ( 632 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1813,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f129,f133,f137,f141,f145,f161,f165,f169,f173,f174,f178,f179,f183,f184,f188,f192,f196,f218,f222,f226,f230,f234,f238,f239,f243,f247,f251,f252,f256,f260,f264,f265,f269,f273,f277,f289,f290,f295,f296,f312,f316,f317,f321,f326,f330,f331,f335,f341,f342,f348,f349,f373,f377,f381,f385,f389,f391,f395,f399,f403,f407,f411,f412,f419,f424,f429,f434,f458,f462,f466,f470,f474,f478,f480,f484,f488,f492,f496,f500,f504,f508,f509,f513,f519,f523,f528,f556,f560,f564,f568,f572,f576,f580,f585,f586,f590,f594,f598,f602,f606,f610,f614,f618,f622,f623,f627,f632,f638,f642,f647,f652,f657,f689,f693,f697,f701,f705,f709,f713,f717,f719,f723,f727,f731,f735,f739,f743,f747,f751,f755,f759,f763,f764,f768,f772,f776,f805,f809,f810,f814,f818,f822,f826,f830,f831,f835,f839,f843,f847,f851,f852,f856,f860,f864,f868,f872,f873,f877,f881,f886,f922,f926,f930,f934,f938,f942,f946,f950,f954,f955,f959,f963,f967,f971,f975,f979,f983,f984,f988,f992,f996,f1000,f1004,f1008,f1012,f1013,f1017,f1021,f1025,f1029,f1033,f1038,f1079,f1083,f1084,f1088,f1092,f1096,f1100,f1104,f1108,f1112,f1113,f1117,f1121,f1125,f1129,f1133,f1137,f1141,f1145,f1149,f1150,f1154,f1158,f1162,f1166,f1170,f1174,f1178,f1182,f1186,f1187,f1191,f1195,f1199,f1203,f1210,f1214,f1215,f1220,f1266,f1270,f1274,f1278,f1282,f1286,f1290,f1294,f1298,f1302,f1306,f1307,f1311,f1315,f1319,f1323,f1327,f1331,f1335,f1339,f1343,f1347,f1351,f1352,f1356,f1360,f1364,f1368,f1372,f1376,f1380,f1384,f1388,f1392,f1396,f1397,f1401,f1405,f1409,f1413,f1417,f1424,f1428,f1429,f1437,f1438,f1600,f1610,f1611,f1615,f1655,f1659,f1663,f1667,f1671,f1675,f1679,f1683,f1684,f1688,f1692,f1696,f1700,f1704,f1708,f1712,f1716,f1720,f1724,f1728,f1729,f1733,f1737,f1741,f1745,f1749,f1753,f1757,f1761,f1765,f1769,f1773,f1774,f1778,f1782,f1786,f1791,f1798,f1802,f1808,f1812])).

fof(f1812,plain,
    ( ~ spl7_66
    | ~ spl7_322
    | spl7_481 ),
    inference(avatar_contradiction_clause,[],[f1811])).

fof(f1811,plain,
    ( $false
    | ~ spl7_66
    | ~ spl7_322
    | ~ spl7_481 ),
    inference(subsumption_resolution,[],[f1810,f1436])).

fof(f1436,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl7_481 ),
    inference(avatar_component_clause,[],[f1435])).

fof(f1435,plain,
    ( spl7_481
  <=> ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_481])])).

fof(f1810,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl7_66
    | ~ spl7_322 ),
    inference(forward_demodulation,[],[f1809,f85])).

fof(f85,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',t71_relat_1)).

fof(f1809,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
    | ~ spl7_66
    | ~ spl7_322 ),
    inference(forward_demodulation,[],[f315,f1020])).

fof(f1020,plain,
    ( k5_relat_1(sK3,sK2) = k6_relat_1(sK1)
    | ~ spl7_322 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f1019,plain,
    ( spl7_322
  <=> k5_relat_1(sK3,sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_322])])).

fof(f315,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK2)),k2_relat_1(sK2))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl7_66
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f1808,plain,
    ( spl7_560
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f1804,f310,f1806])).

fof(f1806,plain,
    ( spl7_560
  <=> m1_subset_1(k2_relat_1(k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_560])])).

fof(f310,plain,
    ( spl7_64
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK2,sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f1804,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_relat_1(sK2)))
    | ~ spl7_64 ),
    inference(unit_resulting_resolution,[],[f311,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',t3_subset)).

fof(f311,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,sK2)),k2_relat_1(sK2))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f310])).

fof(f1802,plain,
    ( ~ spl7_559
    | spl7_483 ),
    inference(avatar_split_clause,[],[f1793,f1598,f1800])).

fof(f1800,plain,
    ( spl7_559
  <=> ~ r2_hidden(sK1,sK4(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_559])])).

fof(f1598,plain,
    ( spl7_483
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_483])])).

fof(f1793,plain,
    ( ~ r2_hidden(sK1,sK4(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK2)))))
    | ~ spl7_483 ),
    inference(unit_resulting_resolution,[],[f88,f1599,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',t4_subset)).

fof(f1599,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(sK2)))
    | ~ spl7_483 ),
    inference(avatar_component_clause,[],[f1598])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',existence_m1_subset_1)).

fof(f1798,plain,
    ( ~ spl7_557
    | spl7_483 ),
    inference(avatar_split_clause,[],[f1794,f1598,f1796])).

fof(f1796,plain,
    ( spl7_557
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_557])])).

fof(f1794,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k2_relat_1(sK2)))
    | ~ spl7_483 ),
    inference(unit_resulting_resolution,[],[f1599,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',t1_subset)).

fof(f1791,plain,
    ( spl7_554
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f1787,f287,f1789])).

fof(f1789,plain,
    ( spl7_554
  <=> m1_subset_1(k2_relat_1(k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_554])])).

fof(f287,plain,
    ( spl7_60
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f1787,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_relat_1(sK3)))
    | ~ spl7_60 ),
    inference(unit_resulting_resolution,[],[f288,f97])).

fof(f288,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),k2_relat_1(sK3))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f287])).

fof(f1786,plain,
    ( spl7_552
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1616,f1608,f655,f630,f1784])).

fof(f1784,plain,
    ( spl7_552
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_552])])).

fof(f630,plain,
    ( spl7_178
  <=> v1_funct_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).

fof(f655,plain,
    ( spl7_188
  <=> m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_188])])).

fof(f1608,plain,
    ( spl7_484
  <=> v1_funct_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_484])])).

fof(f1616,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),k5_relat_1(sK3,sK3)))
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f631,f656,f113,f1609,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',dt_k1_partfun1)).

fof(f1609,plain,
    ( v1_funct_1(k6_relat_1(sK1))
    | ~ spl7_484 ),
    inference(avatar_component_clause,[],[f1608])).

fof(f113,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',redefinition_k6_partfun1)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',dt_k6_partfun1)).

fof(f656,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_188 ),
    inference(avatar_component_clause,[],[f655])).

fof(f631,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ spl7_178 ),
    inference(avatar_component_clause,[],[f630])).

fof(f1782,plain,
    ( spl7_550
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1617,f1608,f1036,f645,f1780])).

fof(f1780,plain,
    ( spl7_550
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_550])])).

fof(f645,plain,
    ( spl7_184
  <=> v1_funct_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_184])])).

fof(f1036,plain,
    ( spl7_330
  <=> m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_330])])).

fof(f1617,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),k5_relat_1(sK2,sK2)))
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f113,f1609,f110])).

fof(f1037,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_330 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f646,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK2))
    | ~ spl7_184 ),
    inference(avatar_component_clause,[],[f645])).

fof(f1778,plain,
    ( spl7_548
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1618,f1608,f1218,f650,f1776])).

fof(f1776,plain,
    ( spl7_548
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK0,k6_relat_1(sK1),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_548])])).

fof(f650,plain,
    ( spl7_186
  <=> v1_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_186])])).

fof(f1218,plain,
    ( spl7_398
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_398])])).

fof(f1618,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK0,k6_relat_1(sK1),k5_relat_1(sK2,sK3)))
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f113,f1609,f110])).

fof(f1219,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_398 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f651,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl7_186 ),
    inference(avatar_component_clause,[],[f650])).

fof(f1774,plain,
    ( spl7_536
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1619,f1608,f1751])).

fof(f1751,plain,
    ( spl7_536
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_536])])).

fof(f1619,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)))
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f1609,f113,f113,f1609,f110])).

fof(f1773,plain,
    ( spl7_546
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1620,f1608,f143,f139,f1771])).

fof(f1771,plain,
    ( spl7_546
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_546])])).

fof(f139,plain,
    ( spl7_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f143,plain,
    ( spl7_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f1620,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),sK2))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f144,f140,f113,f1609,f110])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f144,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1769,plain,
    ( spl7_544
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1621,f1608,f135,f131,f1767])).

fof(f1767,plain,
    ( spl7_544
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_544])])).

fof(f131,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f135,plain,
    ( spl7_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1621,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),sK3))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f136,f132,f113,f1609,f110])).

fof(f132,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f136,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1765,plain,
    ( spl7_542
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1622,f1608,f655,f630,f1763])).

fof(f1763,plain,
    ( spl7_542
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_542])])).

fof(f1622,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k6_relat_1(sK1)))
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f631,f656,f113,f1609,f110])).

fof(f1761,plain,
    ( spl7_540
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1623,f1608,f1036,f645,f1759])).

fof(f1759,plain,
    ( spl7_540
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_540])])).

fof(f1623,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k6_relat_1(sK1)))
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f113,f1609,f110])).

fof(f1757,plain,
    ( spl7_538
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1624,f1608,f1218,f650,f1755])).

fof(f1755,plain,
    ( spl7_538
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_538])])).

fof(f1624,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k6_relat_1(sK1)))
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f113,f1609,f110])).

fof(f1753,plain,
    ( spl7_536
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1625,f1608,f1751])).

fof(f1625,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)))
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f1609,f113,f113,f1609,f110])).

fof(f1749,plain,
    ( spl7_534
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1626,f1608,f143,f139,f1747])).

fof(f1747,plain,
    ( spl7_534
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_534])])).

fof(f1626,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f144,f140,f113,f1609,f110])).

fof(f1745,plain,
    ( spl7_532
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1627,f1608,f135,f131,f1743])).

fof(f1743,plain,
    ( spl7_532
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_532])])).

fof(f1627,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k6_relat_1(sK1)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f136,f132,f113,f1609,f110])).

fof(f1741,plain,
    ( spl7_530
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1628,f1608,f655,f630,f1739])).

fof(f1739,plain,
    ( spl7_530
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_530])])).

fof(f1628,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f631,f656,f113,f1609,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1737,plain,
    ( spl7_528
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1629,f1608,f1036,f645,f1735])).

fof(f1735,plain,
    ( spl7_528
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_528])])).

fof(f1629,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f113,f1609,f111])).

fof(f1733,plain,
    ( spl7_526
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1630,f1608,f1218,f650,f1731])).

fof(f1731,plain,
    ( spl7_526
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK0,k6_relat_1(sK1),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_526])])).

fof(f1630,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK0,k6_relat_1(sK1),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f113,f1609,f111])).

fof(f1729,plain,
    ( spl7_514
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1631,f1608,f1706])).

fof(f1706,plain,
    ( spl7_514
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_514])])).

fof(f1631,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f1609,f113,f113,f1609,f111])).

fof(f1728,plain,
    ( spl7_524
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1632,f1608,f143,f139,f1726])).

fof(f1726,plain,
    ( spl7_524
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_524])])).

fof(f1632,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f144,f140,f113,f1609,f111])).

fof(f1724,plain,
    ( spl7_522
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1633,f1608,f135,f131,f1722])).

fof(f1722,plain,
    ( spl7_522
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_522])])).

fof(f1633,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f136,f132,f113,f1609,f111])).

fof(f1720,plain,
    ( spl7_520
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1634,f1608,f655,f630,f1718])).

fof(f1718,plain,
    ( spl7_520
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_520])])).

fof(f1634,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f631,f656,f113,f1609,f111])).

fof(f1716,plain,
    ( spl7_518
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1635,f1608,f1036,f645,f1714])).

fof(f1714,plain,
    ( spl7_518
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_518])])).

fof(f1635,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f113,f1609,f111])).

fof(f1712,plain,
    ( spl7_516
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1636,f1608,f1218,f650,f1710])).

fof(f1710,plain,
    ( spl7_516
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_516])])).

fof(f1636,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f113,f1609,f111])).

fof(f1708,plain,
    ( spl7_514
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1637,f1608,f1706])).

fof(f1637,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f1609,f113,f113,f1609,f111])).

fof(f1704,plain,
    ( spl7_512
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1638,f1608,f143,f139,f1702])).

fof(f1702,plain,
    ( spl7_512
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_512])])).

fof(f1638,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f144,f140,f113,f1609,f111])).

fof(f1700,plain,
    ( spl7_510
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1639,f1608,f135,f131,f1698])).

fof(f1698,plain,
    ( spl7_510
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_510])])).

fof(f1639,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k6_relat_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f136,f132,f113,f1609,f111])).

fof(f1696,plain,
    ( spl7_508
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1640,f1608,f655,f630,f1694])).

fof(f1694,plain,
    ( spl7_508
  <=> k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),k5_relat_1(sK3,sK3)) = k5_relat_1(k6_relat_1(sK1),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_508])])).

fof(f1640,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),k5_relat_1(sK3,sK3)) = k5_relat_1(k6_relat_1(sK1),k5_relat_1(sK3,sK3))
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f631,f656,f113,f1609,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',redefinition_k1_partfun1)).

fof(f1692,plain,
    ( spl7_506
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1641,f1608,f1036,f645,f1690])).

fof(f1690,plain,
    ( spl7_506
  <=> k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),k5_relat_1(sK2,sK2)) = k5_relat_1(k6_relat_1(sK1),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_506])])).

fof(f1641,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),k5_relat_1(sK2,sK2)) = k5_relat_1(k6_relat_1(sK1),k5_relat_1(sK2,sK2))
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f113,f1609,f109])).

fof(f1688,plain,
    ( spl7_504
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1642,f1608,f1218,f650,f1686])).

fof(f1686,plain,
    ( spl7_504
  <=> k1_partfun1(sK1,sK1,sK0,sK0,k6_relat_1(sK1),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_relat_1(sK1),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_504])])).

fof(f1642,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK0,k6_relat_1(sK1),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_relat_1(sK1),k5_relat_1(sK2,sK3))
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f113,f1609,f109])).

fof(f1684,plain,
    ( spl7_492
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1643,f1608,f1661])).

fof(f1661,plain,
    ( spl7_492
  <=> k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_492])])).

fof(f1643,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK1))
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f1609,f113,f113,f1609,f109])).

fof(f1683,plain,
    ( spl7_502
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1644,f1608,f143,f139,f1681])).

fof(f1681,plain,
    ( spl7_502
  <=> k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),sK2) = k5_relat_1(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_502])])).

fof(f1644,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK1,k6_relat_1(sK1),sK2) = k5_relat_1(k6_relat_1(sK1),sK2)
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f144,f140,f113,f1609,f109])).

fof(f1679,plain,
    ( spl7_500
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1645,f1608,f135,f131,f1677])).

fof(f1677,plain,
    ( spl7_500
  <=> k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),sK3) = k5_relat_1(k6_relat_1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_500])])).

fof(f1645,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k6_relat_1(sK1),sK3) = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f136,f132,f113,f1609,f109])).

fof(f1675,plain,
    ( spl7_498
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1646,f1608,f655,f630,f1673])).

fof(f1673,plain,
    ( spl7_498
  <=> k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k6_relat_1(sK1)) = k5_relat_1(k5_relat_1(sK3,sK3),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_498])])).

fof(f1646,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k6_relat_1(sK1)) = k5_relat_1(k5_relat_1(sK3,sK3),k6_relat_1(sK1))
    | ~ spl7_178
    | ~ spl7_188
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f631,f656,f113,f1609,f109])).

fof(f1671,plain,
    ( spl7_496
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1647,f1608,f1036,f645,f1669])).

fof(f1669,plain,
    ( spl7_496
  <=> k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k6_relat_1(sK1)) = k5_relat_1(k5_relat_1(sK2,sK2),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_496])])).

fof(f1647,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k6_relat_1(sK1)) = k5_relat_1(k5_relat_1(sK2,sK2),k6_relat_1(sK1))
    | ~ spl7_184
    | ~ spl7_330
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f113,f1609,f109])).

fof(f1667,plain,
    ( spl7_494
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1648,f1608,f1218,f650,f1665])).

fof(f1665,plain,
    ( spl7_494
  <=> k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k6_relat_1(sK1)) = k5_relat_1(k5_relat_1(sK2,sK3),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_494])])).

fof(f1648,plain,
    ( k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k6_relat_1(sK1)) = k5_relat_1(k5_relat_1(sK2,sK3),k6_relat_1(sK1))
    | ~ spl7_186
    | ~ spl7_398
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f113,f1609,f109])).

fof(f1663,plain,
    ( spl7_492
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1649,f1608,f1661])).

fof(f1649,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK1))
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f1609,f113,f113,f1609,f109])).

fof(f1659,plain,
    ( spl7_490
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1650,f1608,f143,f139,f1657])).

fof(f1657,plain,
    ( spl7_490
  <=> k1_partfun1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_490])])).

fof(f1650,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(sK1))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f144,f140,f113,f1609,f109])).

fof(f1655,plain,
    ( spl7_488
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f1651,f1608,f135,f131,f1653])).

fof(f1653,plain,
    ( spl7_488
  <=> k1_partfun1(sK1,sK0,sK1,sK1,sK3,k6_relat_1(sK1)) = k5_relat_1(sK3,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_488])])).

fof(f1651,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK1,sK3,k6_relat_1(sK1)) = k5_relat_1(sK3,k6_relat_1(sK1))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_484 ),
    inference(unit_resulting_resolution,[],[f136,f132,f113,f1609,f109])).

fof(f1615,plain,
    ( spl7_486
    | ~ spl7_48
    | ~ spl7_322 ),
    inference(avatar_split_clause,[],[f1605,f1019,f254,f1613])).

fof(f1613,plain,
    ( spl7_486
  <=> k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_486])])).

fof(f254,plain,
    ( spl7_48
  <=> k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f1605,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k6_relat_1(sK1)
    | ~ spl7_48
    | ~ spl7_322 ),
    inference(backward_demodulation,[],[f1020,f255])).

fof(f255,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f254])).

fof(f1611,plain,
    ( spl7_396
    | ~ spl7_182
    | ~ spl7_322 ),
    inference(avatar_split_clause,[],[f1604,f1019,f640,f1212])).

fof(f1212,plain,
    ( spl7_396
  <=> r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_396])])).

fof(f640,plain,
    ( spl7_182
  <=> r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_182])])).

fof(f1604,plain,
    ( r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1))
    | ~ spl7_182
    | ~ spl7_322 ),
    inference(backward_demodulation,[],[f1020,f641])).

fof(f641,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))
    | ~ spl7_182 ),
    inference(avatar_component_clause,[],[f640])).

fof(f1610,plain,
    ( spl7_484
    | ~ spl7_180
    | ~ spl7_322 ),
    inference(avatar_split_clause,[],[f1603,f1019,f636,f1608])).

fof(f636,plain,
    ( spl7_180
  <=> v1_funct_1(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_180])])).

fof(f1603,plain,
    ( v1_funct_1(k6_relat_1(sK1))
    | ~ spl7_180
    | ~ spl7_322 ),
    inference(backward_demodulation,[],[f1020,f637])).

fof(f637,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK2))
    | ~ spl7_180 ),
    inference(avatar_component_clause,[],[f636])).

fof(f1600,plain,
    ( ~ spl7_483
    | spl7_481 ),
    inference(avatar_split_clause,[],[f1596,f1435,f1598])).

fof(f1596,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(sK2)))
    | ~ spl7_481 ),
    inference(unit_resulting_resolution,[],[f1436,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f1438,plain,
    ( ~ spl7_481
    | spl7_139
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f1432,f526,f521,f1435])).

fof(f521,plain,
    ( spl7_139
  <=> k2_relat_1(sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).

fof(f526,plain,
    ( spl7_140
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f1432,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl7_139
    | ~ spl7_140 ),
    inference(unit_resulting_resolution,[],[f522,f527,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',d10_xboole_0)).

fof(f527,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl7_140 ),
    inference(avatar_component_clause,[],[f526])).

fof(f522,plain,
    ( k2_relat_1(sK2) != sK1
    | ~ spl7_139 ),
    inference(avatar_component_clause,[],[f521])).

fof(f1437,plain,
    ( ~ spl7_481
    | spl7_139
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f1433,f526,f521,f1435])).

fof(f1433,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl7_139
    | ~ spl7_140 ),
    inference(unit_resulting_resolution,[],[f522,f527,f95])).

fof(f1429,plain,
    ( spl7_402
    | ~ spl7_398
    | spl7_405 ),
    inference(avatar_split_clause,[],[f1418,f1272,f1218,f1268])).

fof(f1268,plain,
    ( spl7_402
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_402])])).

fof(f1272,plain,
    ( spl7_405
  <=> ~ sP6(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_405])])).

fof(f1418,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_398
    | ~ spl7_405 ),
    inference(unit_resulting_resolution,[],[f1219,f1273,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f119_D])).

fof(f119_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP6(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f1273,plain,
    ( ~ sP6(sK0,sK0)
    | ~ spl7_405 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f1428,plain,
    ( spl7_478
    | spl7_405 ),
    inference(avatar_split_clause,[],[f1419,f1272,f1426])).

fof(f1426,plain,
    ( spl7_478
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_478])])).

fof(f1419,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl7_405 ),
    inference(unit_resulting_resolution,[],[f113,f1273,f119])).

fof(f1424,plain,
    ( spl7_476
    | spl7_405 ),
    inference(avatar_split_clause,[],[f1420,f1272,f1422])).

fof(f1422,plain,
    ( spl7_476
  <=> r2_relset_1(sK0,sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_476])])).

fof(f1420,plain,
    ( r2_relset_1(sK0,sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl7_405 ),
    inference(unit_resulting_resolution,[],[f88,f1273,f119])).

fof(f1417,plain,
    ( spl7_474
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1222,f1218,f1415])).

fof(f1415,plain,
    ( spl7_474
  <=> k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3)) = k2_relat_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_474])])).

fof(f1222,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3)) = k2_relat_1(k5_relat_1(sK2,sK3))
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f1219,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',redefinition_k2_relset_1)).

fof(f1413,plain,
    ( spl7_472
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1223,f1218,f1411])).

fof(f1411,plain,
    ( spl7_472
  <=> m1_subset_1(k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_472])])).

fof(f1223,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3)),k1_zfmisc_1(sK0))
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f1219,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',dt_k2_relset_1)).

fof(f1409,plain,
    ( spl7_470
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1224,f1218,f655,f650,f630,f1407])).

fof(f1407,plain,
    ( spl7_470
  <=> k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_470])])).

fof(f1224,plain,
    ( k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f631,f656,f651,f1219,f109])).

fof(f1405,plain,
    ( spl7_468
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1225,f1218,f884,f650,f636,f1403])).

fof(f1403,plain,
    ( spl7_468
  <=> k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_468])])).

fof(f884,plain,
    ( spl7_272
  <=> m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_272])])).

fof(f1225,plain,
    ( k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2))
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f637,f885,f651,f1219,f109])).

fof(f885,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_272 ),
    inference(avatar_component_clause,[],[f884])).

fof(f1401,plain,
    ( spl7_466
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1226,f1218,f1036,f650,f645,f1399])).

fof(f1399,plain,
    ( spl7_466
  <=> k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_466])])).

fof(f1226,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2))
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f651,f1219,f109])).

fof(f1397,plain,
    ( spl7_454
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1227,f1218,f650,f1374])).

fof(f1374,plain,
    ( spl7_454
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_454])])).

fof(f1227,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f651,f1219,f109])).

fof(f1396,plain,
    ( spl7_464
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1228,f1218,f650,f143,f139,f1394])).

fof(f1394,plain,
    ( spl7_464
  <=> k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2) = k5_relat_1(k5_relat_1(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_464])])).

fof(f1228,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2) = k5_relat_1(k5_relat_1(sK2,sK3),sK2)
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f144,f140,f651,f1219,f109])).

fof(f1392,plain,
    ( spl7_462
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1229,f1218,f650,f135,f131,f1390])).

fof(f1390,plain,
    ( spl7_462
  <=> k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3) = k5_relat_1(k5_relat_1(sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_462])])).

fof(f1229,plain,
    ( k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3) = k5_relat_1(k5_relat_1(sK2,sK3),sK3)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f136,f132,f651,f1219,f109])).

fof(f1388,plain,
    ( spl7_460
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1230,f1218,f655,f650,f630,f1386])).

fof(f1386,plain,
    ( spl7_460
  <=> k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_460])])).

fof(f1230,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f631,f656,f651,f1219,f109])).

fof(f1384,plain,
    ( spl7_458
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1231,f1218,f884,f650,f636,f1382])).

fof(f1382,plain,
    ( spl7_458
  <=> k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_458])])).

fof(f1231,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3))
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f637,f885,f651,f1219,f109])).

fof(f1380,plain,
    ( spl7_456
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1232,f1218,f1036,f650,f645,f1378])).

fof(f1378,plain,
    ( spl7_456
  <=> k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_456])])).

fof(f1232,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f651,f1219,f109])).

fof(f1376,plain,
    ( spl7_454
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1233,f1218,f650,f1374])).

fof(f1233,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f651,f1219,f109])).

fof(f1372,plain,
    ( spl7_452
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1234,f1218,f650,f143,f139,f1370])).

fof(f1370,plain,
    ( spl7_452
  <=> k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)) = k5_relat_1(sK2,k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_452])])).

fof(f1234,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)) = k5_relat_1(sK2,k5_relat_1(sK2,sK3))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f144,f140,f651,f1219,f109])).

fof(f1368,plain,
    ( spl7_450
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1235,f1218,f650,f135,f131,f1366])).

fof(f1366,plain,
    ( spl7_450
  <=> k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)) = k5_relat_1(sK3,k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_450])])).

fof(f1235,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)) = k5_relat_1(sK3,k5_relat_1(sK2,sK3))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f136,f132,f651,f1219,f109])).

fof(f1364,plain,
    ( spl7_448
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1236,f1218,f655,f650,f630,f1362])).

fof(f1362,plain,
    ( spl7_448
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_448])])).

fof(f1236,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f631,f656,f651,f1219,f110])).

fof(f1360,plain,
    ( spl7_446
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1237,f1218,f884,f650,f636,f1358])).

fof(f1358,plain,
    ( spl7_446
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_446])])).

fof(f1237,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)))
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f637,f885,f651,f1219,f110])).

fof(f1356,plain,
    ( spl7_444
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1238,f1218,f1036,f650,f645,f1354])).

fof(f1354,plain,
    ( spl7_444
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_444])])).

fof(f1238,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)))
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f651,f1219,f110])).

fof(f1352,plain,
    ( spl7_432
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1239,f1218,f650,f1329])).

fof(f1329,plain,
    ( spl7_432
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_432])])).

fof(f1239,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f651,f1219,f110])).

fof(f1351,plain,
    ( spl7_442
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1240,f1218,f650,f143,f139,f1349])).

fof(f1349,plain,
    ( spl7_442
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_442])])).

fof(f1240,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f144,f140,f651,f1219,f110])).

fof(f1347,plain,
    ( spl7_440
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1241,f1218,f650,f135,f131,f1345])).

fof(f1345,plain,
    ( spl7_440
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_440])])).

fof(f1241,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f136,f132,f651,f1219,f110])).

fof(f1343,plain,
    ( spl7_438
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1242,f1218,f655,f650,f630,f1341])).

fof(f1341,plain,
    ( spl7_438
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_438])])).

fof(f1242,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f631,f656,f651,f1219,f110])).

fof(f1339,plain,
    ( spl7_436
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1243,f1218,f884,f650,f636,f1337])).

fof(f1337,plain,
    ( spl7_436
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_436])])).

fof(f1243,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)))
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f637,f885,f651,f1219,f110])).

fof(f1335,plain,
    ( spl7_434
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1244,f1218,f1036,f650,f645,f1333])).

fof(f1333,plain,
    ( spl7_434
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_434])])).

fof(f1244,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)))
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f651,f1219,f110])).

fof(f1331,plain,
    ( spl7_432
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1245,f1218,f650,f1329])).

fof(f1245,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f651,f1219,f110])).

fof(f1327,plain,
    ( spl7_430
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1246,f1218,f650,f143,f139,f1325])).

fof(f1325,plain,
    ( spl7_430
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_430])])).

fof(f1246,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f144,f140,f651,f1219,f110])).

fof(f1323,plain,
    ( spl7_428
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1247,f1218,f650,f135,f131,f1321])).

fof(f1321,plain,
    ( spl7_428
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_428])])).

fof(f1247,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f136,f132,f651,f1219,f110])).

fof(f1319,plain,
    ( spl7_426
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1248,f1218,f655,f650,f630,f1317])).

fof(f1317,plain,
    ( spl7_426
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_426])])).

fof(f1248,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f631,f656,f651,f1219,f111])).

fof(f1315,plain,
    ( spl7_424
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1249,f1218,f884,f650,f636,f1313])).

fof(f1313,plain,
    ( spl7_424
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_424])])).

fof(f1249,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f637,f885,f651,f1219,f111])).

fof(f1311,plain,
    ( spl7_422
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1250,f1218,f1036,f650,f645,f1309])).

fof(f1309,plain,
    ( spl7_422
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_422])])).

fof(f1250,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f651,f1219,f111])).

fof(f1307,plain,
    ( spl7_410
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1251,f1218,f650,f1284])).

fof(f1284,plain,
    ( spl7_410
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_410])])).

fof(f1251,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f651,f1219,f111])).

fof(f1306,plain,
    ( spl7_420
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1252,f1218,f650,f143,f139,f1304])).

fof(f1304,plain,
    ( spl7_420
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_420])])).

fof(f1252,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f144,f140,f651,f1219,f111])).

fof(f1302,plain,
    ( spl7_418
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1253,f1218,f650,f135,f131,f1300])).

fof(f1300,plain,
    ( spl7_418
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_418])])).

fof(f1253,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f136,f132,f651,f1219,f111])).

fof(f1298,plain,
    ( spl7_416
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1254,f1218,f655,f650,f630,f1296])).

fof(f1296,plain,
    ( spl7_416
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_416])])).

fof(f1254,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_178
    | ~ spl7_186
    | ~ spl7_188
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f631,f656,f651,f1219,f111])).

fof(f1294,plain,
    ( spl7_414
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1255,f1218,f884,f650,f636,f1292])).

fof(f1292,plain,
    ( spl7_414
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_414])])).

fof(f1255,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_180
    | ~ spl7_186
    | ~ spl7_272
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f637,f885,f651,f1219,f111])).

fof(f1290,plain,
    ( spl7_412
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1256,f1218,f1036,f650,f645,f1288])).

fof(f1288,plain,
    ( spl7_412
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_412])])).

fof(f1256,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_184
    | ~ spl7_186
    | ~ spl7_330
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f651,f1219,f111])).

fof(f1286,plain,
    ( spl7_410
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1257,f1218,f650,f1284])).

fof(f1257,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f651,f1219,f651,f1219,f111])).

fof(f1282,plain,
    ( spl7_408
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1258,f1218,f650,f143,f139,f1280])).

fof(f1280,plain,
    ( spl7_408
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_408])])).

fof(f1258,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f144,f140,f651,f1219,f111])).

fof(f1278,plain,
    ( spl7_406
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1259,f1218,f650,f135,f131,f1276])).

fof(f1276,plain,
    ( spl7_406
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_406])])).

fof(f1259,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_186
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f136,f132,f651,f1219,f111])).

fof(f1274,plain,
    ( ~ spl7_405
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1260,f1218,f1272])).

fof(f1260,plain,
    ( ~ sP6(sK0,sK0)
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f1219,f120])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f105,f119_D])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',reflexivity_r2_relset_1)).

fof(f1270,plain,
    ( spl7_402
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1261,f1218,f1268])).

fof(f1261,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f1219,f121])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',redefinition_r2_relset_1)).

fof(f1266,plain,
    ( spl7_400
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f1262,f1218,f1264])).

fof(f1264,plain,
    ( spl7_400
  <=> r1_tarski(k5_relat_1(sK2,sK3),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_400])])).

fof(f1262,plain,
    ( r1_tarski(k5_relat_1(sK2,sK3),k2_zfmisc_1(sK0,sK0))
    | ~ spl7_398 ),
    inference(unit_resulting_resolution,[],[f1219,f96])).

fof(f1220,plain,
    ( spl7_398
    | ~ spl7_40
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f1216,f262,f236,f1218])).

fof(f236,plain,
    ( spl7_40
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f262,plain,
    ( spl7_52
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f1216,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_40
    | ~ spl7_52 ),
    inference(forward_demodulation,[],[f237,f263])).

fof(f263,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f262])).

fof(f237,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f236])).

fof(f1215,plain,
    ( spl7_276
    | ~ spl7_272
    | spl7_279 ),
    inference(avatar_split_clause,[],[f1204,f928,f884,f924])).

fof(f924,plain,
    ( spl7_276
  <=> r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_276])])).

fof(f928,plain,
    ( spl7_279
  <=> ~ sP6(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_279])])).

fof(f1204,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_272
    | ~ spl7_279 ),
    inference(unit_resulting_resolution,[],[f885,f929,f119])).

fof(f929,plain,
    ( ~ sP6(sK1,sK1)
    | ~ spl7_279 ),
    inference(avatar_component_clause,[],[f928])).

fof(f1214,plain,
    ( spl7_396
    | spl7_279 ),
    inference(avatar_split_clause,[],[f1205,f928,f1212])).

fof(f1205,plain,
    ( r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1))
    | ~ spl7_279 ),
    inference(unit_resulting_resolution,[],[f113,f929,f119])).

fof(f1210,plain,
    ( spl7_394
    | spl7_279 ),
    inference(avatar_split_clause,[],[f1206,f928,f1208])).

fof(f1208,plain,
    ( spl7_394
  <=> r2_relset_1(sK1,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_394])])).

fof(f1206,plain,
    ( r2_relset_1(sK1,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))))
    | ~ spl7_279 ),
    inference(unit_resulting_resolution,[],[f88,f929,f119])).

fof(f1203,plain,
    ( spl7_392
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1040,f1036,f1201])).

fof(f1201,plain,
    ( spl7_392
  <=> k2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)) = k2_relat_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_392])])).

fof(f1040,plain,
    ( k2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)) = k2_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f1037,f101])).

fof(f1199,plain,
    ( spl7_390
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1041,f1036,f1197])).

fof(f1197,plain,
    ( spl7_390
  <=> m1_subset_1(k2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_390])])).

fof(f1041,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK1))
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f1037,f102])).

fof(f1195,plain,
    ( spl7_388
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1042,f1036,f655,f645,f630,f1193])).

fof(f1193,plain,
    ( spl7_388
  <=> k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_388])])).

fof(f1042,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3))
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f631,f656,f646,f1037,f109])).

fof(f1191,plain,
    ( spl7_386
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1043,f1036,f884,f645,f636,f1189])).

fof(f1189,plain,
    ( spl7_386
  <=> k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_386])])).

fof(f1043,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f637,f885,f646,f1037,f109])).

fof(f1187,plain,
    ( spl7_376
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1044,f1036,f645,f1168])).

fof(f1168,plain,
    ( spl7_376
  <=> k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_376])])).

fof(f1044,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f646,f1037,f109])).

fof(f1186,plain,
    ( spl7_384
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1045,f1036,f645,f143,f139,f1184])).

fof(f1184,plain,
    ( spl7_384
  <=> k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2) = k5_relat_1(k5_relat_1(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_384])])).

fof(f1045,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2) = k5_relat_1(k5_relat_1(sK2,sK2),sK2)
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f144,f140,f646,f1037,f109])).

fof(f1182,plain,
    ( spl7_382
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1046,f1036,f645,f135,f131,f1180])).

fof(f1180,plain,
    ( spl7_382
  <=> k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3) = k5_relat_1(k5_relat_1(sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_382])])).

fof(f1046,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3) = k5_relat_1(k5_relat_1(sK2,sK2),sK3)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f136,f132,f646,f1037,f109])).

fof(f1178,plain,
    ( spl7_380
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1047,f1036,f655,f645,f630,f1176])).

fof(f1176,plain,
    ( spl7_380
  <=> k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_380])])).

fof(f1047,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2))
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f631,f656,f646,f1037,f109])).

fof(f1174,plain,
    ( spl7_378
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1048,f1036,f884,f645,f636,f1172])).

fof(f1172,plain,
    ( spl7_378
  <=> k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_378])])).

fof(f1048,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f637,f885,f646,f1037,f109])).

fof(f1170,plain,
    ( spl7_376
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1049,f1036,f645,f1168])).

fof(f1049,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f646,f1037,f109])).

fof(f1166,plain,
    ( spl7_374
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1050,f1036,f645,f143,f139,f1164])).

fof(f1164,plain,
    ( spl7_374
  <=> k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)) = k5_relat_1(sK2,k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_374])])).

fof(f1050,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)) = k5_relat_1(sK2,k5_relat_1(sK2,sK2))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f144,f140,f646,f1037,f109])).

fof(f1162,plain,
    ( spl7_372
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1051,f1036,f645,f135,f131,f1160])).

fof(f1160,plain,
    ( spl7_372
  <=> k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_372])])).

fof(f1051,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,sK2))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f136,f132,f646,f1037,f109])).

fof(f1158,plain,
    ( spl7_370
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1052,f1036,f655,f645,f630,f1156])).

fof(f1156,plain,
    ( spl7_370
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_370])])).

fof(f1052,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)))
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f631,f656,f646,f1037,f110])).

fof(f1154,plain,
    ( spl7_368
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1053,f1036,f884,f645,f636,f1152])).

fof(f1152,plain,
    ( spl7_368
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_368])])).

fof(f1053,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f637,f885,f646,f1037,f110])).

fof(f1150,plain,
    ( spl7_358
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1054,f1036,f645,f1131])).

fof(f1131,plain,
    ( spl7_358
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_358])])).

fof(f1054,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f646,f1037,f110])).

fof(f1149,plain,
    ( spl7_366
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1055,f1036,f645,f143,f139,f1147])).

fof(f1147,plain,
    ( spl7_366
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_366])])).

fof(f1055,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f144,f140,f646,f1037,f110])).

fof(f1145,plain,
    ( spl7_364
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1056,f1036,f645,f135,f131,f1143])).

fof(f1143,plain,
    ( spl7_364
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_364])])).

fof(f1056,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f136,f132,f646,f1037,f110])).

fof(f1141,plain,
    ( spl7_362
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1057,f1036,f655,f645,f630,f1139])).

fof(f1139,plain,
    ( spl7_362
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_362])])).

fof(f1057,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)))
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f631,f656,f646,f1037,f110])).

fof(f1137,plain,
    ( spl7_360
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1058,f1036,f884,f645,f636,f1135])).

fof(f1135,plain,
    ( spl7_360
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_360])])).

fof(f1058,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f637,f885,f646,f1037,f110])).

fof(f1133,plain,
    ( spl7_358
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1059,f1036,f645,f1131])).

fof(f1059,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f646,f1037,f110])).

fof(f1129,plain,
    ( spl7_356
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1060,f1036,f645,f143,f139,f1127])).

fof(f1127,plain,
    ( spl7_356
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_356])])).

fof(f1060,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f144,f140,f646,f1037,f110])).

fof(f1125,plain,
    ( spl7_354
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1061,f1036,f645,f135,f131,f1123])).

fof(f1123,plain,
    ( spl7_354
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_354])])).

fof(f1061,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f136,f132,f646,f1037,f110])).

fof(f1121,plain,
    ( spl7_352
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1062,f1036,f655,f645,f630,f1119])).

fof(f1119,plain,
    ( spl7_352
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_352])])).

fof(f1062,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f631,f656,f646,f1037,f111])).

fof(f1117,plain,
    ( spl7_350
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1063,f1036,f884,f645,f636,f1115])).

fof(f1115,plain,
    ( spl7_350
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_350])])).

fof(f1063,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f637,f885,f646,f1037,f111])).

fof(f1113,plain,
    ( spl7_340
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1064,f1036,f645,f1094])).

fof(f1094,plain,
    ( spl7_340
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_340])])).

fof(f1064,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f646,f1037,f111])).

fof(f1112,plain,
    ( spl7_348
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1065,f1036,f645,f143,f139,f1110])).

fof(f1110,plain,
    ( spl7_348
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_348])])).

fof(f1065,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f144,f140,f646,f1037,f111])).

fof(f1108,plain,
    ( spl7_346
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1066,f1036,f645,f135,f131,f1106])).

fof(f1106,plain,
    ( spl7_346
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_346])])).

fof(f1066,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f136,f132,f646,f1037,f111])).

fof(f1104,plain,
    ( spl7_344
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1067,f1036,f655,f645,f630,f1102])).

fof(f1102,plain,
    ( spl7_344
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_344])])).

fof(f1067,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_178
    | ~ spl7_184
    | ~ spl7_188
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f631,f656,f646,f1037,f111])).

fof(f1100,plain,
    ( spl7_342
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1068,f1036,f884,f645,f636,f1098])).

fof(f1098,plain,
    ( spl7_342
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_342])])).

fof(f1068,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_180
    | ~ spl7_184
    | ~ spl7_272
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f637,f885,f646,f1037,f111])).

fof(f1096,plain,
    ( spl7_340
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1069,f1036,f645,f1094])).

fof(f1069,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f646,f1037,f646,f1037,f111])).

fof(f1092,plain,
    ( spl7_338
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1070,f1036,f645,f143,f139,f1090])).

fof(f1090,plain,
    ( spl7_338
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_338])])).

fof(f1070,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f144,f140,f646,f1037,f111])).

fof(f1088,plain,
    ( spl7_336
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1071,f1036,f645,f135,f131,f1086])).

fof(f1086,plain,
    ( spl7_336
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_336])])).

fof(f1071,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_184
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f136,f132,f646,f1037,f111])).

fof(f1084,plain,
    ( spl7_334
    | spl7_35
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1072,f1036,f224,f1081])).

fof(f1081,plain,
    ( spl7_334
  <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_334])])).

fof(f224,plain,
    ( spl7_35
  <=> ~ sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1072,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_35
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f225,f1037,f119])).

fof(f225,plain,
    ( ~ sP6(sK1,sK0)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f224])).

fof(f1083,plain,
    ( spl7_334
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1074,f1036,f1081])).

fof(f1074,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f1037,f121])).

fof(f1079,plain,
    ( spl7_332
    | ~ spl7_330 ),
    inference(avatar_split_clause,[],[f1075,f1036,f1077])).

fof(f1077,plain,
    ( spl7_332
  <=> r1_tarski(k5_relat_1(sK2,sK2),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_332])])).

fof(f1075,plain,
    ( r1_tarski(k5_relat_1(sK2,sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl7_330 ),
    inference(unit_resulting_resolution,[],[f1037,f96])).

fof(f1038,plain,
    ( spl7_330
    | ~ spl7_38
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f1034,f258,f232,f1036])).

fof(f232,plain,
    ( spl7_38
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f258,plain,
    ( spl7_50
  <=> k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f1034,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_38
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f233,f259])).

fof(f259,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f258])).

fof(f233,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f232])).

fof(f1033,plain,
    ( spl7_328
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f888,f884,f1031])).

fof(f1031,plain,
    ( spl7_328
  <=> k2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2)) = k2_relat_1(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_328])])).

fof(f888,plain,
    ( k2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2)) = k2_relat_1(k5_relat_1(sK3,sK2))
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f885,f101])).

fof(f1029,plain,
    ( spl7_326
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f889,f884,f1027])).

fof(f1027,plain,
    ( spl7_326
  <=> m1_subset_1(k2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_326])])).

fof(f889,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2)),k1_zfmisc_1(sK1))
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f885,f102])).

fof(f1025,plain,
    ( spl7_324
    | ~ spl7_182
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f890,f884,f640,f1023])).

fof(f1023,plain,
    ( spl7_324
  <=> r2_relset_1(sK1,sK1,k6_relat_1(sK1),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_324])])).

fof(f890,plain,
    ( r2_relset_1(sK1,sK1,k6_relat_1(sK1),k5_relat_1(sK3,sK2))
    | ~ spl7_182
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f113,f641,f885,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | r2_relset_1(X0,X1,X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',symmetry_r2_relset_1)).

fof(f1021,plain,
    ( spl7_322
    | ~ spl7_182
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f891,f884,f640,f1019])).

fof(f891,plain,
    ( k5_relat_1(sK3,sK2) = k6_relat_1(sK1)
    | ~ spl7_182
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f113,f641,f885,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1017,plain,
    ( spl7_320
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f892,f884,f655,f636,f630,f1015])).

fof(f1015,plain,
    ( spl7_320
  <=> k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_320])])).

fof(f892,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f631,f656,f637,f885,f109])).

fof(f1013,plain,
    ( spl7_312
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f893,f884,f636,f998])).

fof(f998,plain,
    ( spl7_312
  <=> k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_312])])).

fof(f893,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f637,f885,f637,f885,f109])).

fof(f1012,plain,
    ( spl7_318
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f894,f884,f636,f143,f139,f1010])).

fof(f1010,plain,
    ( spl7_318
  <=> k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2) = k5_relat_1(k5_relat_1(sK3,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_318])])).

fof(f894,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2) = k5_relat_1(k5_relat_1(sK3,sK2),sK2)
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f144,f140,f637,f885,f109])).

fof(f1008,plain,
    ( spl7_316
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f895,f884,f636,f135,f131,f1006])).

fof(f1006,plain,
    ( spl7_316
  <=> k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(k5_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_316])])).

fof(f895,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(k5_relat_1(sK3,sK2),sK3)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f136,f132,f637,f885,f109])).

fof(f1004,plain,
    ( spl7_314
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f896,f884,f655,f636,f630,f1002])).

fof(f1002,plain,
    ( spl7_314
  <=> k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_314])])).

fof(f896,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2))
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f631,f656,f637,f885,f109])).

fof(f1000,plain,
    ( spl7_312
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f897,f884,f636,f998])).

fof(f897,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f637,f885,f637,f885,f109])).

fof(f996,plain,
    ( spl7_310
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f898,f884,f636,f143,f139,f994])).

fof(f994,plain,
    ( spl7_310
  <=> k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(sK2,k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_310])])).

fof(f898,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(sK2,k5_relat_1(sK3,sK2))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f144,f140,f637,f885,f109])).

fof(f992,plain,
    ( spl7_308
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f899,f884,f636,f135,f131,f990])).

fof(f990,plain,
    ( spl7_308
  <=> k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_308])])).

fof(f899,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,k5_relat_1(sK3,sK2))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f136,f132,f637,f885,f109])).

fof(f988,plain,
    ( spl7_306
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f900,f884,f655,f636,f630,f986])).

fof(f986,plain,
    ( spl7_306
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_306])])).

fof(f900,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)))
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f631,f656,f637,f885,f110])).

fof(f984,plain,
    ( spl7_298
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f901,f884,f636,f969])).

fof(f969,plain,
    ( spl7_298
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_298])])).

fof(f901,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f637,f885,f637,f885,f110])).

fof(f983,plain,
    ( spl7_304
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f902,f884,f636,f143,f139,f981])).

fof(f981,plain,
    ( spl7_304
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_304])])).

fof(f902,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f144,f140,f637,f885,f110])).

fof(f979,plain,
    ( spl7_302
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f903,f884,f636,f135,f131,f977])).

fof(f977,plain,
    ( spl7_302
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_302])])).

fof(f903,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f136,f132,f637,f885,f110])).

fof(f975,plain,
    ( spl7_300
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f904,f884,f655,f636,f630,f973])).

fof(f973,plain,
    ( spl7_300
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_300])])).

fof(f904,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)))
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f631,f656,f637,f885,f110])).

fof(f971,plain,
    ( spl7_298
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f905,f884,f636,f969])).

fof(f905,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f637,f885,f637,f885,f110])).

fof(f967,plain,
    ( spl7_296
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f906,f884,f636,f143,f139,f965])).

fof(f965,plain,
    ( spl7_296
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_296])])).

fof(f906,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f144,f140,f637,f885,f110])).

fof(f963,plain,
    ( spl7_294
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f907,f884,f636,f135,f131,f961])).

fof(f961,plain,
    ( spl7_294
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_294])])).

fof(f907,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f136,f132,f637,f885,f110])).

fof(f959,plain,
    ( spl7_292
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f908,f884,f655,f636,f630,f957])).

fof(f957,plain,
    ( spl7_292
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_292])])).

fof(f908,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f631,f656,f637,f885,f111])).

fof(f955,plain,
    ( spl7_284
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f909,f884,f636,f940])).

fof(f940,plain,
    ( spl7_284
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_284])])).

fof(f909,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f637,f885,f637,f885,f111])).

fof(f954,plain,
    ( spl7_290
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f910,f884,f636,f143,f139,f952])).

fof(f952,plain,
    ( spl7_290
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_290])])).

fof(f910,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f144,f140,f637,f885,f111])).

fof(f950,plain,
    ( spl7_288
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f911,f884,f636,f135,f131,f948])).

fof(f948,plain,
    ( spl7_288
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_288])])).

fof(f911,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f136,f132,f637,f885,f111])).

fof(f946,plain,
    ( spl7_286
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f912,f884,f655,f636,f630,f944])).

fof(f944,plain,
    ( spl7_286
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_286])])).

fof(f912,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_178
    | ~ spl7_180
    | ~ spl7_188
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f631,f656,f637,f885,f111])).

fof(f942,plain,
    ( spl7_284
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f913,f884,f636,f940])).

fof(f913,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f637,f885,f637,f885,f111])).

fof(f938,plain,
    ( spl7_282
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f914,f884,f636,f143,f139,f936])).

fof(f936,plain,
    ( spl7_282
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_282])])).

fof(f914,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f144,f140,f637,f885,f111])).

fof(f934,plain,
    ( spl7_280
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f915,f884,f636,f135,f131,f932])).

fof(f932,plain,
    ( spl7_280
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_280])])).

fof(f915,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_180
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f136,f132,f637,f885,f111])).

fof(f930,plain,
    ( ~ spl7_279
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f916,f884,f928])).

fof(f916,plain,
    ( ~ sP6(sK1,sK1)
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f885,f120])).

fof(f926,plain,
    ( spl7_276
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f917,f884,f924])).

fof(f917,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f885,f121])).

fof(f922,plain,
    ( spl7_274
    | ~ spl7_272 ),
    inference(avatar_split_clause,[],[f918,f884,f920])).

fof(f920,plain,
    ( spl7_274
  <=> r1_tarski(k5_relat_1(sK3,sK2),k2_zfmisc_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_274])])).

fof(f918,plain,
    ( r1_tarski(k5_relat_1(sK3,sK2),k2_zfmisc_1(sK1,sK1))
    | ~ spl7_272 ),
    inference(unit_resulting_resolution,[],[f885,f96])).

fof(f886,plain,
    ( spl7_272
    | ~ spl7_36
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f882,f254,f228,f884])).

fof(f228,plain,
    ( spl7_36
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f882,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_36
    | ~ spl7_48 ),
    inference(forward_demodulation,[],[f229,f255])).

fof(f229,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f228])).

fof(f881,plain,
    ( spl7_270
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f778,f655,f879])).

fof(f879,plain,
    ( spl7_270
  <=> k2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_270])])).

fof(f778,plain,
    ( k2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f656,f101])).

fof(f877,plain,
    ( spl7_268
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f779,f655,f875])).

fof(f875,plain,
    ( spl7_268
  <=> m1_subset_1(k2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_268])])).

fof(f779,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK0))
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f656,f102])).

fof(f873,plain,
    ( spl7_262
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f780,f655,f630,f862])).

fof(f862,plain,
    ( spl7_262
  <=> k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_262])])).

fof(f780,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f631,f656,f631,f656,f109])).

fof(f872,plain,
    ( spl7_266
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f781,f655,f630,f143,f139,f870])).

fof(f870,plain,
    ( spl7_266
  <=> k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2) = k5_relat_1(k5_relat_1(sK3,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_266])])).

fof(f781,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2) = k5_relat_1(k5_relat_1(sK3,sK3),sK2)
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f144,f140,f631,f656,f109])).

fof(f868,plain,
    ( spl7_264
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f782,f655,f630,f135,f131,f866])).

fof(f866,plain,
    ( spl7_264
  <=> k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3) = k5_relat_1(k5_relat_1(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_264])])).

fof(f782,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3) = k5_relat_1(k5_relat_1(sK3,sK3),sK3)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f136,f132,f631,f656,f109])).

fof(f864,plain,
    ( spl7_262
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f783,f655,f630,f862])).

fof(f783,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f631,f656,f631,f656,f109])).

fof(f860,plain,
    ( spl7_260
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f784,f655,f630,f143,f139,f858])).

fof(f858,plain,
    ( spl7_260
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_260])])).

fof(f784,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,sK3))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f144,f140,f631,f656,f109])).

fof(f856,plain,
    ( spl7_258
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f785,f655,f630,f135,f131,f854])).

fof(f854,plain,
    ( spl7_258
  <=> k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)) = k5_relat_1(sK3,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).

fof(f785,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)) = k5_relat_1(sK3,k5_relat_1(sK3,sK3))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f136,f132,f631,f656,f109])).

fof(f852,plain,
    ( spl7_252
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f786,f655,f630,f841])).

fof(f841,plain,
    ( spl7_252
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_252])])).

fof(f786,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f631,f656,f631,f656,f110])).

fof(f851,plain,
    ( spl7_256
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f787,f655,f630,f143,f139,f849])).

fof(f849,plain,
    ( spl7_256
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_256])])).

fof(f787,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f144,f140,f631,f656,f110])).

fof(f847,plain,
    ( spl7_254
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f788,f655,f630,f135,f131,f845])).

fof(f845,plain,
    ( spl7_254
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_254])])).

fof(f788,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f136,f132,f631,f656,f110])).

fof(f843,plain,
    ( spl7_252
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f789,f655,f630,f841])).

fof(f789,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f631,f656,f631,f656,f110])).

fof(f839,plain,
    ( spl7_250
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f790,f655,f630,f143,f139,f837])).

fof(f837,plain,
    ( spl7_250
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_250])])).

fof(f790,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f144,f140,f631,f656,f110])).

fof(f835,plain,
    ( spl7_248
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f791,f655,f630,f135,f131,f833])).

fof(f833,plain,
    ( spl7_248
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_248])])).

fof(f791,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f136,f132,f631,f656,f110])).

fof(f831,plain,
    ( spl7_242
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f792,f655,f630,f820])).

fof(f820,plain,
    ( spl7_242
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_242])])).

fof(f792,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f631,f656,f631,f656,f111])).

fof(f830,plain,
    ( spl7_246
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f793,f655,f630,f143,f139,f828])).

fof(f828,plain,
    ( spl7_246
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_246])])).

fof(f793,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f144,f140,f631,f656,f111])).

fof(f826,plain,
    ( spl7_244
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f794,f655,f630,f135,f131,f824])).

fof(f824,plain,
    ( spl7_244
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_244])])).

fof(f794,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f136,f132,f631,f656,f111])).

fof(f822,plain,
    ( spl7_242
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f795,f655,f630,f820])).

fof(f795,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f631,f656,f631,f656,f111])).

fof(f818,plain,
    ( spl7_240
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f796,f655,f630,f143,f139,f816])).

fof(f816,plain,
    ( spl7_240
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_240])])).

fof(f796,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f144,f140,f631,f656,f111])).

fof(f814,plain,
    ( spl7_238
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f797,f655,f630,f135,f131,f812])).

fof(f812,plain,
    ( spl7_238
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_238])])).

fof(f797,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_178
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f136,f132,f631,f656,f111])).

fof(f810,plain,
    ( spl7_236
    | spl7_17
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f798,f655,f167,f807])).

fof(f807,plain,
    ( spl7_236
  <=> r2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_236])])).

fof(f167,plain,
    ( spl7_17
  <=> ~ sP6(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f798,plain,
    ( r2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_17
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f168,f656,f119])).

fof(f168,plain,
    ( ~ sP6(sK0,sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f809,plain,
    ( spl7_236
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f800,f655,f807])).

fof(f800,plain,
    ( r2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f656,f121])).

fof(f805,plain,
    ( spl7_234
    | ~ spl7_188 ),
    inference(avatar_split_clause,[],[f801,f655,f803])).

fof(f803,plain,
    ( spl7_234
  <=> r1_tarski(k5_relat_1(sK3,sK3),k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_234])])).

fof(f801,plain,
    ( r1_tarski(k5_relat_1(sK3,sK3),k2_zfmisc_1(sK1,sK0))
    | ~ spl7_188 ),
    inference(unit_resulting_resolution,[],[f656,f96])).

fof(f776,plain,
    ( spl7_232
    | ~ spl7_62
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f658,f333,f293,f774])).

fof(f774,plain,
    ( spl7_232
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_232])])).

fof(f293,plain,
    ( spl7_62
  <=> v1_relat_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f333,plain,
    ( spl7_74
  <=> v1_relat_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f658,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_62
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f294,f334,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',dt_k5_relat_1)).

fof(f334,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f333])).

fof(f294,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f293])).

fof(f772,plain,
    ( spl7_230
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f659,f333,f328,f770])).

fof(f770,plain,
    ( spl7_230
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_230])])).

fof(f328,plain,
    ( spl7_72
  <=> v1_relat_1(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f659,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)))
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f329,f334,f92])).

fof(f329,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2))
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f328])).

fof(f768,plain,
    ( spl7_228
    | ~ spl7_70
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f660,f333,f324,f766])).

fof(f766,plain,
    ( spl7_228
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_228])])).

fof(f324,plain,
    ( spl7_70
  <=> v1_relat_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f660,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)))
    | ~ spl7_70
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f325,f334,f92])).

fof(f325,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f324])).

fof(f764,plain,
    ( spl7_216
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f661,f333,f741])).

fof(f741,plain,
    ( spl7_216
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).

fof(f661,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f334,f334,f92])).

fof(f763,plain,
    ( spl7_226
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f663,f333,f275,f761])).

fof(f761,plain,
    ( spl7_226
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_226])])).

fof(f275,plain,
    ( spl7_58
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f663,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),sK2))
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f276,f334,f92])).

fof(f276,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f275])).

fof(f759,plain,
    ( spl7_224
    | ~ spl7_28
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f664,f333,f194,f757])).

fof(f757,plain,
    ( spl7_224
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).

fof(f194,plain,
    ( spl7_28
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f664,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),sK3))
    | ~ spl7_28
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f195,f334,f92])).

fof(f195,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f194])).

fof(f755,plain,
    ( spl7_222
    | ~ spl7_62
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f665,f333,f293,f753])).

fof(f753,plain,
    ( spl7_222
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_222])])).

fof(f665,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_62
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f294,f334,f92])).

fof(f751,plain,
    ( spl7_220
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f666,f333,f328,f749])).

fof(f749,plain,
    ( spl7_220
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_220])])).

fof(f666,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)))
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f329,f334,f92])).

fof(f747,plain,
    ( spl7_218
    | ~ spl7_70
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f667,f333,f324,f745])).

fof(f745,plain,
    ( spl7_218
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f667,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)))
    | ~ spl7_70
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f325,f334,f92])).

fof(f743,plain,
    ( spl7_216
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f668,f333,f741])).

fof(f668,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f334,f334,f92])).

fof(f739,plain,
    ( spl7_214
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f670,f333,f275,f737])).

fof(f737,plain,
    ( spl7_214
  <=> v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).

fof(f670,plain,
    ( v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK3)))
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f276,f334,f92])).

fof(f735,plain,
    ( spl7_212
    | ~ spl7_28
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f671,f333,f194,f733])).

fof(f733,plain,
    ( spl7_212
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_212])])).

fof(f671,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK2,sK3)))
    | ~ spl7_28
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f195,f334,f92])).

fof(f731,plain,
    ( spl7_210
    | ~ spl7_62
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f672,f333,f293,f729])).

fof(f729,plain,
    ( spl7_210
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_210])])).

fof(f672,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3)))
    | ~ spl7_62
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f294,f334,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',t45_relat_1)).

fof(f727,plain,
    ( spl7_208
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f673,f333,f328,f725])).

fof(f725,plain,
    ( spl7_208
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_208])])).

fof(f673,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2)))
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f329,f334,f87])).

fof(f723,plain,
    ( spl7_206
    | ~ spl7_70
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f674,f333,f324,f721])).

fof(f721,plain,
    ( spl7_206
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_206])])).

fof(f674,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2)))
    | ~ spl7_70
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f325,f334,f87])).

fof(f719,plain,
    ( spl7_194
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f675,f333,f695])).

fof(f695,plain,
    ( spl7_194
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_194])])).

fof(f675,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3)))
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f334,f334,f87])).

fof(f717,plain,
    ( spl7_204
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f677,f333,f275,f715])).

fof(f715,plain,
    ( spl7_204
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_204])])).

fof(f677,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),sK2)),k2_relat_1(sK2))
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f276,f334,f87])).

fof(f713,plain,
    ( spl7_202
    | ~ spl7_28
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f678,f333,f194,f711])).

fof(f711,plain,
    ( spl7_202
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_202])])).

fof(f678,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),sK3)),k2_relat_1(sK3))
    | ~ spl7_28
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f195,f334,f87])).

fof(f709,plain,
    ( spl7_200
    | ~ spl7_62
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f679,f333,f293,f707])).

fof(f707,plain,
    ( spl7_200
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_200])])).

fof(f679,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3)))
    | ~ spl7_62
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f294,f334,f87])).

fof(f705,plain,
    ( spl7_198
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f680,f333,f328,f703])).

fof(f703,plain,
    ( spl7_198
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_198])])).

fof(f680,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3)))
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f329,f334,f87])).

fof(f701,plain,
    ( spl7_196
    | ~ spl7_70
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f681,f333,f324,f699])).

fof(f699,plain,
    ( spl7_196
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).

fof(f681,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3)))
    | ~ spl7_70
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f325,f334,f87])).

fof(f697,plain,
    ( spl7_194
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f682,f333,f695])).

fof(f682,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3)))
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f334,f334,f87])).

fof(f693,plain,
    ( spl7_192
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f684,f333,f275,f691])).

fof(f691,plain,
    ( spl7_192
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_192])])).

fof(f684,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3)))
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f276,f334,f87])).

fof(f689,plain,
    ( spl7_190
    | ~ spl7_28
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f685,f333,f194,f687])).

fof(f687,plain,
    ( spl7_190
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).

fof(f685,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK2,sK3))),k2_relat_1(k5_relat_1(sK2,sK3)))
    | ~ spl7_28
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f195,f334,f87])).

fof(f657,plain,
    ( spl7_188
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f653,f181,f171,f655])).

fof(f171,plain,
    ( spl7_18
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f181,plain,
    ( spl7_22
  <=> k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3) = k5_relat_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f653,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f172,f182])).

fof(f182,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f172,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f652,plain,
    ( spl7_186
    | ~ spl7_46
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f648,f262,f249,f650])).

fof(f249,plain,
    ( spl7_46
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f648,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl7_46
    | ~ spl7_52 ),
    inference(backward_demodulation,[],[f263,f250])).

fof(f250,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f249])).

fof(f647,plain,
    ( spl7_184
    | ~ spl7_44
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f643,f258,f245,f645])).

fof(f245,plain,
    ( spl7_44
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f643,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK2))
    | ~ spl7_44
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f259,f246])).

fof(f246,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f245])).

fof(f642,plain,
    ( spl7_182
    | ~ spl7_2
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f634,f254,f127,f640])).

fof(f127,plain,
    ( spl7_2
  <=> r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f634,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k6_relat_1(sK1))
    | ~ spl7_2
    | ~ spl7_48 ),
    inference(backward_demodulation,[],[f255,f128])).

fof(f128,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f638,plain,
    ( spl7_180
    | ~ spl7_42
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f633,f254,f241,f636])).

fof(f241,plain,
    ( spl7_42
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f633,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK2))
    | ~ spl7_42
    | ~ spl7_48 ),
    inference(backward_demodulation,[],[f255,f242])).

fof(f242,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f241])).

fof(f632,plain,
    ( spl7_178
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f628,f181,f176,f630])).

fof(f176,plain,
    ( spl7_20
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f628,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f182,f177])).

fof(f177,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f627,plain,
    ( spl7_176
    | ~ spl7_62
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f529,f328,f293,f625])).

fof(f625,plain,
    ( spl7_176
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_176])])).

fof(f529,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)))
    | ~ spl7_62
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f294,f329,f92])).

fof(f623,plain,
    ( spl7_166
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f530,f328,f604])).

fof(f604,plain,
    ( spl7_166
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f530,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f329,f329,f92])).

fof(f622,plain,
    ( spl7_174
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f531,f328,f324,f620])).

fof(f620,plain,
    ( spl7_174
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).

fof(f531,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f325,f329,f92])).

fof(f618,plain,
    ( spl7_172
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f533,f328,f275,f616])).

fof(f616,plain,
    ( spl7_172
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f533,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),sK2))
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f276,f329,f92])).

fof(f614,plain,
    ( spl7_170
    | ~ spl7_28
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f534,f328,f194,f612])).

fof(f612,plain,
    ( spl7_170
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).

fof(f534,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),sK3))
    | ~ spl7_28
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f195,f329,f92])).

fof(f610,plain,
    ( spl7_168
    | ~ spl7_62
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f535,f328,f293,f608])).

fof(f608,plain,
    ( spl7_168
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f535,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)))
    | ~ spl7_62
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f294,f329,f92])).

fof(f606,plain,
    ( spl7_166
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f536,f328,f604])).

fof(f536,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f329,f329,f92])).

fof(f602,plain,
    ( spl7_164
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f537,f328,f324,f600])).

fof(f600,plain,
    ( spl7_164
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_164])])).

fof(f537,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f325,f329,f92])).

fof(f598,plain,
    ( spl7_162
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f539,f328,f275,f596])).

fof(f596,plain,
    ( spl7_162
  <=> v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f539,plain,
    ( v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK2)))
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f276,f329,f92])).

fof(f594,plain,
    ( spl7_160
    | ~ spl7_28
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f540,f328,f194,f592])).

fof(f592,plain,
    ( spl7_160
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f540,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK2)))
    | ~ spl7_28
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f195,f329,f92])).

fof(f590,plain,
    ( spl7_158
    | ~ spl7_62
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f541,f328,f293,f588])).

fof(f588,plain,
    ( spl7_158
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f541,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3)))
    | ~ spl7_62
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f294,f329,f87])).

fof(f586,plain,
    ( spl7_148
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f542,f328,f566])).

fof(f566,plain,
    ( spl7_148
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f542,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2)))
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f329,f329,f87])).

fof(f585,plain,
    ( spl7_156
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f543,f328,f324,f583])).

fof(f583,plain,
    ( spl7_156
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f543,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2)))
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f325,f329,f87])).

fof(f580,plain,
    ( spl7_154
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f545,f328,f275,f578])).

fof(f578,plain,
    ( spl7_154
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f545,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),sK2)),k2_relat_1(sK2))
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f276,f329,f87])).

fof(f576,plain,
    ( spl7_152
    | ~ spl7_28
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f546,f328,f194,f574])).

fof(f574,plain,
    ( spl7_152
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f546,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),sK3)),k2_relat_1(sK3))
    | ~ spl7_28
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f195,f329,f87])).

fof(f572,plain,
    ( spl7_150
    | ~ spl7_62
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f547,f328,f293,f570])).

fof(f570,plain,
    ( spl7_150
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f547,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2)))
    | ~ spl7_62
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f294,f329,f87])).

fof(f568,plain,
    ( spl7_148
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f548,f328,f566])).

fof(f548,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2)))
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f329,f329,f87])).

fof(f564,plain,
    ( spl7_146
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f549,f328,f324,f562])).

fof(f562,plain,
    ( spl7_146
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f549,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2)))
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f325,f329,f87])).

fof(f560,plain,
    ( spl7_144
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f551,f328,f275,f558])).

fof(f558,plain,
    ( spl7_144
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f551,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2)))
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f276,f329,f87])).

fof(f556,plain,
    ( spl7_142
    | ~ spl7_28
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f552,f328,f194,f554])).

fof(f554,plain,
    ( spl7_142
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f552,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK2))),k2_relat_1(k5_relat_1(sK3,sK2)))
    | ~ spl7_28
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f195,f329,f87])).

fof(f528,plain,
    ( spl7_140
    | ~ spl7_136 ),
    inference(avatar_split_clause,[],[f524,f517,f526])).

fof(f517,plain,
    ( spl7_136
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f524,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl7_136 ),
    inference(unit_resulting_resolution,[],[f518,f96])).

fof(f518,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl7_136 ),
    inference(avatar_component_clause,[],[f517])).

fof(f523,plain,
    ( ~ spl7_139
    | spl7_1
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f515,f271,f123,f521])).

fof(f123,plain,
    ( spl7_1
  <=> k2_relset_1(sK0,sK1,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f271,plain,
    ( spl7_56
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f515,plain,
    ( k2_relat_1(sK2) != sK1
    | ~ spl7_1
    | ~ spl7_56 ),
    inference(superposition,[],[f124,f272])).

fof(f272,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f271])).

fof(f124,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f519,plain,
    ( spl7_136
    | ~ spl7_54
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f514,f271,f267,f517])).

fof(f267,plain,
    ( spl7_54
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f514,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl7_54
    | ~ spl7_56 ),
    inference(backward_demodulation,[],[f272,f268])).

fof(f268,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f267])).

fof(f513,plain,
    ( spl7_134
    | ~ spl7_62
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f435,f324,f293,f511])).

fof(f511,plain,
    ( spl7_134
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f435,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)))
    | ~ spl7_62
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f294,f325,f92])).

fof(f509,plain,
    ( spl7_126
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f436,f324,f494])).

fof(f494,plain,
    ( spl7_126
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f436,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f325,f325,f92])).

fof(f508,plain,
    ( spl7_132
    | ~ spl7_58
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f438,f324,f275,f506])).

fof(f506,plain,
    ( spl7_132
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f438,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK2))
    | ~ spl7_58
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f276,f325,f92])).

fof(f504,plain,
    ( spl7_130
    | ~ spl7_28
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f439,f324,f194,f502])).

fof(f502,plain,
    ( spl7_130
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f439,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK3))
    | ~ spl7_28
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f195,f325,f92])).

fof(f500,plain,
    ( spl7_128
    | ~ spl7_62
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f440,f324,f293,f498])).

fof(f498,plain,
    ( spl7_128
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f440,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)))
    | ~ spl7_62
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f294,f325,f92])).

fof(f496,plain,
    ( spl7_126
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f441,f324,f494])).

fof(f441,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f325,f325,f92])).

fof(f492,plain,
    ( spl7_124
    | ~ spl7_58
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f443,f324,f275,f490])).

fof(f490,plain,
    ( spl7_124
  <=> v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f443,plain,
    ( v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK2)))
    | ~ spl7_58
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f276,f325,f92])).

fof(f488,plain,
    ( spl7_122
    | ~ spl7_28
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f444,f324,f194,f486])).

fof(f486,plain,
    ( spl7_122
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f444,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK2,sK2)))
    | ~ spl7_28
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f195,f325,f92])).

fof(f484,plain,
    ( spl7_120
    | ~ spl7_62
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f445,f324,f293,f482])).

fof(f482,plain,
    ( spl7_120
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f445,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3)))
    | ~ spl7_62
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f294,f325,f87])).

fof(f480,plain,
    ( spl7_112
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f446,f324,f464])).

fof(f464,plain,
    ( spl7_112
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f446,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2)))
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f325,f325,f87])).

fof(f478,plain,
    ( spl7_118
    | ~ spl7_58
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f448,f324,f275,f476])).

fof(f476,plain,
    ( spl7_118
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f448,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK2)),k2_relat_1(sK2))
    | ~ spl7_58
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f276,f325,f87])).

fof(f474,plain,
    ( spl7_116
    | ~ spl7_28
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f449,f324,f194,f472])).

fof(f472,plain,
    ( spl7_116
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f449,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK3)),k2_relat_1(sK3))
    | ~ spl7_28
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f195,f325,f87])).

fof(f470,plain,
    ( spl7_114
    | ~ spl7_62
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f450,f324,f293,f468])).

fof(f468,plain,
    ( spl7_114
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f450,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2)))
    | ~ spl7_62
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f294,f325,f87])).

fof(f466,plain,
    ( spl7_112
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f451,f324,f464])).

fof(f451,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2)))
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f325,f325,f87])).

fof(f462,plain,
    ( spl7_110
    | ~ spl7_58
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f453,f324,f275,f460])).

fof(f460,plain,
    ( spl7_110
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f453,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2)))
    | ~ spl7_58
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f276,f325,f87])).

fof(f458,plain,
    ( spl7_108
    | ~ spl7_28
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f454,f324,f194,f456])).

fof(f456,plain,
    ( spl7_108
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f454,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK2,sK2))),k2_relat_1(k5_relat_1(sK2,sK2)))
    | ~ spl7_28
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f195,f325,f87])).

fof(f434,plain,
    ( spl7_106
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f430,f267,f432])).

fof(f432,plain,
    ( spl7_106
  <=> r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f430,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)
    | ~ spl7_54 ),
    inference(unit_resulting_resolution,[],[f268,f96])).

fof(f429,plain,
    ( spl7_104
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f425,f422,f427])).

fof(f427,plain,
    ( spl7_104
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f422,plain,
    ( spl7_102
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f425,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl7_102 ),
    inference(unit_resulting_resolution,[],[f423,f96])).

fof(f423,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f422])).

fof(f424,plain,
    ( spl7_102
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f420,f190,f186,f422])).

fof(f186,plain,
    ( spl7_24
  <=> m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f190,plain,
    ( spl7_26
  <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f420,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(backward_demodulation,[],[f191,f187])).

fof(f187,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f191,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f190])).

fof(f419,plain,
    ( spl7_100
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f415,f186,f417])).

fof(f417,plain,
    ( spl7_100
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f415,plain,
    ( r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f187,f96])).

fof(f412,plain,
    ( spl7_94
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f354,f293,f401])).

fof(f401,plain,
    ( spl7_94
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f354,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f294,f294,f92])).

fof(f411,plain,
    ( spl7_98
    | ~ spl7_58
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f356,f293,f275,f409])).

fof(f409,plain,
    ( spl7_98
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f356,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK2))
    | ~ spl7_58
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f276,f294,f92])).

fof(f407,plain,
    ( spl7_96
    | ~ spl7_28
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f357,f293,f194,f405])).

fof(f405,plain,
    ( spl7_96
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f357,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3))
    | ~ spl7_28
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f195,f294,f92])).

fof(f403,plain,
    ( spl7_94
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f358,f293,f401])).

fof(f358,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f294,f294,f92])).

fof(f399,plain,
    ( spl7_92
    | ~ spl7_58
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f360,f293,f275,f397])).

fof(f397,plain,
    ( spl7_92
  <=> v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f360,plain,
    ( v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK3)))
    | ~ spl7_58
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f276,f294,f92])).

fof(f395,plain,
    ( spl7_90
    | ~ spl7_28
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f361,f293,f194,f393])).

fof(f393,plain,
    ( spl7_90
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f361,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))
    | ~ spl7_28
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f195,f294,f92])).

fof(f391,plain,
    ( spl7_84
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f362,f293,f379])).

fof(f379,plain,
    ( spl7_84
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f362,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3)))
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f294,f294,f87])).

fof(f389,plain,
    ( spl7_88
    | ~ spl7_58
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f364,f293,f275,f387])).

fof(f387,plain,
    ( spl7_88
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f364,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK2)),k2_relat_1(sK2))
    | ~ spl7_58
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f276,f294,f87])).

fof(f385,plain,
    ( spl7_86
    | ~ spl7_28
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f365,f293,f194,f383])).

fof(f383,plain,
    ( spl7_86
  <=> r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f365,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3)),k2_relat_1(sK3))
    | ~ spl7_28
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f195,f294,f87])).

fof(f381,plain,
    ( spl7_84
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f366,f293,f379])).

fof(f366,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3)))
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f294,f294,f87])).

fof(f377,plain,
    ( spl7_82
    | ~ spl7_58
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f368,f293,f275,f375])).

fof(f375,plain,
    ( spl7_82
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f368,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3)))
    | ~ spl7_58
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f276,f294,f87])).

fof(f373,plain,
    ( spl7_80
    | ~ spl7_28
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f369,f293,f194,f371])).

fof(f371,plain,
    ( spl7_80
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f369,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,sK3)))
    | ~ spl7_28
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f195,f294,f87])).

fof(f349,plain,
    ( spl7_32
    | ~ spl7_8
    | spl7_35 ),
    inference(avatar_split_clause,[],[f343,f224,f139,f220])).

fof(f220,plain,
    ( spl7_32
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f343,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_8
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f140,f225,f119])).

fof(f348,plain,
    ( spl7_78
    | spl7_35 ),
    inference(avatar_split_clause,[],[f344,f224,f346])).

fof(f346,plain,
    ( spl7_78
  <=> r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f344,plain,
    ( r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f88,f225,f119])).

fof(f342,plain,
    ( spl7_14
    | ~ spl7_4
    | spl7_17 ),
    inference(avatar_split_clause,[],[f336,f167,f131,f163])).

fof(f163,plain,
    ( spl7_14
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f336,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f132,f168,f119])).

fof(f341,plain,
    ( spl7_76
    | spl7_17 ),
    inference(avatar_split_clause,[],[f337,f167,f339])).

fof(f339,plain,
    ( spl7_76
  <=> r2_relset_1(sK1,sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f337,plain,
    ( r2_relset_1(sK1,sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f88,f168,f119])).

fof(f335,plain,
    ( spl7_74
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f298,f275,f194,f333])).

fof(f298,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f195,f276,f92])).

fof(f331,plain,
    ( spl7_70
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f299,f275,f324])).

fof(f299,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f276,f276,f92])).

fof(f330,plain,
    ( spl7_72
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f301,f275,f194,f328])).

fof(f301,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2))
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f195,f276,f92])).

fof(f326,plain,
    ( spl7_70
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f302,f275,f324])).

fof(f302,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f276,f276,f92])).

fof(f321,plain,
    ( spl7_68
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f304,f275,f194,f319])).

fof(f319,plain,
    ( spl7_68
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f304,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f195,f276,f87])).

fof(f317,plain,
    ( spl7_64
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f305,f275,f310])).

fof(f305,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,sK2)),k2_relat_1(sK2))
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f276,f276,f87])).

fof(f316,plain,
    ( spl7_66
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f307,f275,f194,f314])).

fof(f307,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK2)),k2_relat_1(sK2))
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f195,f276,f87])).

fof(f312,plain,
    ( spl7_64
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f308,f275,f310])).

fof(f308,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,sK2)),k2_relat_1(sK2))
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f276,f276,f87])).

fof(f296,plain,
    ( spl7_62
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f279,f194,f293])).

fof(f279,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f195,f195,f92])).

fof(f295,plain,
    ( spl7_62
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f281,f194,f293])).

fof(f281,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f195,f195,f92])).

fof(f290,plain,
    ( spl7_60
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f283,f194,f287])).

fof(f283,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),k2_relat_1(sK3))
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f195,f195,f87])).

fof(f289,plain,
    ( spl7_60
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f285,f194,f287])).

fof(f285,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),k2_relat_1(sK3))
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f195,f195,f87])).

fof(f277,plain,
    ( spl7_58
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f197,f139,f275])).

fof(f197,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f140,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',cc1_relset_1)).

fof(f273,plain,
    ( spl7_56
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f198,f139,f271])).

fof(f198,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f140,f101])).

fof(f269,plain,
    ( spl7_54
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f199,f139,f267])).

fof(f199,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f140,f102])).

fof(f265,plain,
    ( spl7_50
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f200,f143,f139,f258])).

fof(f200,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f144,f140,f140,f109])).

fof(f264,plain,
    ( spl7_52
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f201,f143,f139,f135,f131,f262])).

fof(f201,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f136,f132,f140,f109])).

fof(f260,plain,
    ( spl7_50
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f202,f143,f139,f258])).

fof(f202,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f144,f140,f140,f109])).

fof(f256,plain,
    ( spl7_48
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f203,f143,f139,f135,f131,f254])).

fof(f203,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f136,f144,f132,f140,f109])).

fof(f252,plain,
    ( spl7_44
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f204,f143,f139,f245])).

fof(f204,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2))
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f144,f140,f140,f110])).

fof(f251,plain,
    ( spl7_46
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f205,f143,f139,f135,f131,f249])).

fof(f205,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f136,f132,f140,f110])).

fof(f247,plain,
    ( spl7_44
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f206,f143,f139,f245])).

fof(f206,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2))
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f144,f140,f140,f110])).

fof(f243,plain,
    ( spl7_42
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f207,f143,f139,f135,f131,f241])).

fof(f207,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f136,f144,f132,f140,f110])).

fof(f239,plain,
    ( spl7_38
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f208,f143,f139,f232])).

fof(f208,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f144,f140,f140,f111])).

fof(f238,plain,
    ( spl7_40
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f209,f143,f139,f135,f131,f236])).

fof(f209,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f136,f132,f140,f111])).

fof(f234,plain,
    ( spl7_38
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f210,f143,f139,f232])).

fof(f210,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f144,f144,f140,f140,f111])).

fof(f230,plain,
    ( spl7_36
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f211,f143,f139,f135,f131,f228])).

fof(f211,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f136,f144,f132,f140,f111])).

fof(f226,plain,
    ( ~ spl7_35
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f212,f139,f224])).

fof(f212,plain,
    ( ~ sP6(sK1,sK0)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f140,f120])).

fof(f222,plain,
    ( spl7_32
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f213,f139,f220])).

fof(f213,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f140,f121])).

fof(f218,plain,
    ( spl7_30
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f214,f139,f216])).

fof(f216,plain,
    ( spl7_30
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f214,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f140,f96])).

fof(f196,plain,
    ( spl7_28
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f146,f131,f194])).

fof(f146,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f132,f100])).

fof(f192,plain,
    ( spl7_26
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f147,f131,f190])).

fof(f147,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f132,f101])).

fof(f188,plain,
    ( spl7_24
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f148,f131,f186])).

fof(f148,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f132,f102])).

fof(f184,plain,
    ( spl7_22
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f149,f135,f131,f181])).

fof(f149,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f136,f136,f132,f132,f109])).

fof(f183,plain,
    ( spl7_22
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f150,f135,f131,f181])).

fof(f150,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f136,f136,f132,f132,f109])).

fof(f179,plain,
    ( spl7_20
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f151,f135,f131,f176])).

fof(f151,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f136,f136,f132,f132,f110])).

fof(f178,plain,
    ( spl7_20
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f152,f135,f131,f176])).

fof(f152,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f136,f136,f132,f132,f110])).

fof(f174,plain,
    ( spl7_18
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f153,f135,f131,f171])).

fof(f153,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f136,f136,f132,f132,f111])).

fof(f173,plain,
    ( spl7_18
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f154,f135,f131,f171])).

fof(f154,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f136,f136,f132,f132,f111])).

fof(f169,plain,
    ( ~ spl7_17
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f155,f131,f167])).

fof(f155,plain,
    ( ~ sP6(sK0,sK1)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f132,f120])).

fof(f165,plain,
    ( spl7_14
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f156,f131,f163])).

fof(f156,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f132,f121])).

fof(f161,plain,
    ( spl7_12
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f157,f131,f159])).

fof(f159,plain,
    ( spl7_12
  <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f157,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f132,f96])).

fof(f145,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f74,f143])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f66,f65])).

fof(f65,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_relset_1(X0,X1,X2) != X1
            & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_relset_1(sK0,sK1,sK2) != sK1
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
     => ( k2_relset_1(X0,X1,X2) != X1
        & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK3,X2),k6_partfun1(X1))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t24_funct_2.p',t24_funct_2)).

fof(f141,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f75,f139])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f137,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f76,f135])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f133,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f77,f131])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f129,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f112,f127])).

fof(f112,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f78,f82])).

fof(f78,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f125,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f79,f123])).

fof(f79,plain,(
    k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
