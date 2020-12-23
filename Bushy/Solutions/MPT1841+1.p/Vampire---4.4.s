%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t6_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:56 EDT 2019

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  799 (2231 expanded)
%              Number of leaves         :  218 ( 935 expanded)
%              Depth                    :   12
%              Number of atoms          : 1891 (5258 expanded)
%              Number of equality atoms :   37 ( 200 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2088,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f276,f283,f290,f297,f304,f311,f318,f325,f332,f339,f346,f353,f360,f367,f374,f381,f388,f395,f402,f409,f416,f423,f430,f437,f444,f451,f458,f465,f472,f481,f493,f504,f514,f537,f550,f570,f580,f590,f597,f607,f617,f627,f647,f665,f673,f681,f688,f696,f714,f722,f739,f747,f773,f784,f795,f796,f797,f798,f799,f800,f801,f802,f803,f810,f827,f835,f849,f857,f868,f884,f891,f910,f918,f926,f940,f952,f960,f970,f988,f996,f1010,f1025,f1033,f1041,f1056,f1072,f1080,f1097,f1105,f1122,f1130,f1150,f1158,f1175,f1178,f1186,f1212,f1220,f1237,f1245,f1262,f1272,f1288,f1297,f1316,f1353,f1362,f1379,f1387,f1442,f1450,f1457,f1465,f1486,f1502,f1514,f1531,f1539,f1547,f1555,f1563,f1572,f1580,f1588,f1596,f1620,f1632,f1640,f1682,f1696,f1707,f1715,f1722,f1749,f1757,f1774,f1782,f1807,f1815,f1851,f1864,f1872,f1877,f1890,f1892,f1900,f1917,f1920,f1950,f1958,f1975,f1983,f2003,f2017,f2018,f2019,f2031,f2039,f2047,f2055,f2072,f2082,f2086])).

fof(f2086,plain,
    ( ~ spl21_2
    | ~ spl21_262
    | ~ spl21_284 ),
    inference(avatar_contradiction_clause,[],[f2085])).

fof(f2085,plain,
    ( $false
    | ~ spl21_2
    | ~ spl21_262
    | ~ spl21_284 ),
    inference(subsumption_resolution,[],[f2084,f282])).

fof(f282,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl21_2 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl21_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_2])])).

fof(f2084,plain,
    ( ~ v1_zfmisc_1(sK0)
    | ~ spl21_262
    | ~ spl21_284 ),
    inference(subsumption_resolution,[],[f2083,f1982])).

fof(f1982,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl21_284 ),
    inference(avatar_component_clause,[],[f1981])).

fof(f1981,plain,
    ( spl21_284
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_284])])).

fof(f2083,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ v1_zfmisc_1(sK0)
    | ~ spl21_262 ),
    inference(subsumption_resolution,[],[f2075,f182])).

fof(f182,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',fc2_xboole_0)).

fof(f2075,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ v1_zfmisc_1(sK0)
    | ~ spl21_262 ),
    inference(resolution,[],[f267,f1814])).

fof(f1814,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl21_262 ),
    inference(avatar_component_clause,[],[f1813])).

fof(f1813,plain,
    ( spl21_262
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_262])])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f211,f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc1_subset_1)).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc2_tex_2)).

fof(f2082,plain,
    ( ~ spl21_2
    | ~ spl21_56
    | ~ spl21_260
    | ~ spl21_284 ),
    inference(avatar_contradiction_clause,[],[f2081])).

fof(f2081,plain,
    ( $false
    | ~ spl21_2
    | ~ spl21_56
    | ~ spl21_260
    | ~ spl21_284 ),
    inference(subsumption_resolution,[],[f2080,f1982])).

fof(f2080,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl21_2
    | ~ spl21_56
    | ~ spl21_260 ),
    inference(forward_demodulation,[],[f2079,f1806])).

fof(f1806,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl21_260 ),
    inference(avatar_component_clause,[],[f1805])).

fof(f1805,plain,
    ( spl21_260
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_260])])).

fof(f2079,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl21_2
    | ~ spl21_56
    | ~ spl21_260 ),
    inference(subsumption_resolution,[],[f2078,f182])).

fof(f2078,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl21_2
    | ~ spl21_56
    | ~ spl21_260 ),
    inference(forward_demodulation,[],[f2077,f1806])).

fof(f2077,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl21_2
    | ~ spl21_56 ),
    inference(subsumption_resolution,[],[f2073,f282])).

fof(f2073,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ v1_zfmisc_1(sK0)
    | ~ spl21_56 ),
    inference(resolution,[],[f267,f471])).

fof(f471,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl21_56 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl21_56
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_56])])).

fof(f2072,plain,
    ( spl21_300
    | ~ spl21_190 ),
    inference(avatar_split_clause,[],[f2064,f1295,f2070])).

fof(f2070,plain,
    ( spl21_300
  <=> v1_zfmisc_1(sK8(sK8(sK2(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_300])])).

fof(f1295,plain,
    ( spl21_190
  <=> v1_zfmisc_1(sK8(sK2(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_190])])).

fof(f2064,plain,
    ( v1_zfmisc_1(sK8(sK8(sK2(o_0_0_xboole_0))))
    | ~ spl21_190 ),
    inference(resolution,[],[f2032,f231])).

fof(f231,plain,(
    ! [X0] : m1_subset_1(sK8(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK8(X0),X0)
      & m1_subset_1(sK8(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f42,f149])).

fof(f149,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK8(X0),X0)
        & m1_subset_1(sK8(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc3_subset_1)).

fof(f2032,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK2(o_0_0_xboole_0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_190 ),
    inference(resolution,[],[f1296,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc5_funct_1)).

fof(f1296,plain,
    ( v1_zfmisc_1(sK8(sK2(o_0_0_xboole_0)))
    | ~ spl21_190 ),
    inference(avatar_component_clause,[],[f1295])).

fof(f2055,plain,
    ( spl21_298
    | ~ spl21_148
    | ~ spl21_150
    | spl21_177 ),
    inference(avatar_split_clause,[],[f2029,f1184,f1023,f1008,f2053])).

fof(f2053,plain,
    ( spl21_298
  <=> v1_zfmisc_1(sK5(sK2(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_298])])).

fof(f1008,plain,
    ( spl21_148
  <=> v1_zfmisc_1(sK2(sK8(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_148])])).

fof(f1023,plain,
    ( spl21_150
  <=> o_0_0_xboole_0 = sK8(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_150])])).

fof(f1184,plain,
    ( spl21_177
  <=> ~ v1_xboole_0(sK2(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_177])])).

fof(f2029,plain,
    ( v1_zfmisc_1(sK5(sK2(o_0_0_xboole_0)))
    | ~ spl21_148
    | ~ spl21_150
    | ~ spl21_177 ),
    inference(subsumption_resolution,[],[f2024,f1185])).

fof(f1185,plain,
    ( ~ v1_xboole_0(sK2(o_0_0_xboole_0))
    | ~ spl21_177 ),
    inference(avatar_component_clause,[],[f1184])).

fof(f2024,plain,
    ( v1_zfmisc_1(sK5(sK2(o_0_0_xboole_0)))
    | v1_xboole_0(sK2(o_0_0_xboole_0))
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(resolution,[],[f1879,f196])).

fof(f196,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( ( v1_subset_1(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f88,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_subset_1(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc4_subset_1)).

fof(f1879,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(o_0_0_xboole_0)))
        | v1_zfmisc_1(X0) )
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(forward_demodulation,[],[f1878,f1024])).

fof(f1024,plain,
    ( o_0_0_xboole_0 = sK8(o_0_0_xboole_0)
    | ~ spl21_150 ),
    inference(avatar_component_clause,[],[f1023])).

fof(f1878,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK8(o_0_0_xboole_0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_148 ),
    inference(resolution,[],[f1009,f201])).

fof(f1009,plain,
    ( v1_zfmisc_1(sK2(sK8(o_0_0_xboole_0)))
    | ~ spl21_148 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f2047,plain,
    ( spl21_296
    | ~ spl21_148
    | ~ spl21_150
    | spl21_177 ),
    inference(avatar_split_clause,[],[f2028,f1184,f1023,f1008,f2045])).

fof(f2045,plain,
    ( spl21_296
  <=> v1_zfmisc_1(sK2(sK2(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_296])])).

fof(f2028,plain,
    ( v1_zfmisc_1(sK2(sK2(o_0_0_xboole_0)))
    | ~ spl21_148
    | ~ spl21_150
    | ~ spl21_177 ),
    inference(subsumption_resolution,[],[f2021,f1185])).

fof(f2021,plain,
    ( v1_zfmisc_1(sK2(sK2(o_0_0_xboole_0)))
    | v1_xboole_0(sK2(o_0_0_xboole_0))
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(resolution,[],[f1879,f188])).

fof(f188,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f85,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc1_subset_1)).

fof(f2039,plain,
    ( spl21_294
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(avatar_split_clause,[],[f2025,f1023,f1008,f2037])).

fof(f2037,plain,
    ( spl21_294
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_294])])).

fof(f2025,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(o_0_0_xboole_0))))
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(resolution,[],[f1879,f228])).

fof(f228,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',existence_m1_subset_1)).

fof(f2031,plain,
    ( spl21_190
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(avatar_split_clause,[],[f2027,f1023,f1008,f1295])).

fof(f2027,plain,
    ( v1_zfmisc_1(sK8(sK2(o_0_0_xboole_0)))
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(resolution,[],[f1879,f231])).

fof(f2019,plain,
    ( spl21_148
    | spl21_146
    | ~ spl21_158
    | ~ spl21_240 ),
    inference(avatar_split_clause,[],[f1874,f1630,f1070,f1002,f1008])).

fof(f1002,plain,
    ( spl21_146
  <=> v1_xboole_0(sK8(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_146])])).

fof(f1070,plain,
    ( spl21_158
  <=> v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_158])])).

fof(f1630,plain,
    ( spl21_240
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_240])])).

fof(f1874,plain,
    ( v1_xboole_0(sK8(o_0_0_xboole_0))
    | v1_zfmisc_1(sK2(sK8(o_0_0_xboole_0)))
    | ~ spl21_158
    | ~ spl21_240 ),
    inference(forward_demodulation,[],[f1827,f1631])).

fof(f1631,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK0))
    | ~ spl21_240 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f1827,plain,
    ( v1_zfmisc_1(sK2(sK8(o_0_0_xboole_0)))
    | v1_xboole_0(sK8(sK6(k1_zfmisc_1(sK0))))
    | ~ spl21_158
    | ~ spl21_240 ),
    inference(forward_demodulation,[],[f1819,f1631])).

fof(f1819,plain,
    ( v1_zfmisc_1(sK2(sK8(sK6(k1_zfmisc_1(sK0)))))
    | v1_xboole_0(sK8(sK6(k1_zfmisc_1(sK0))))
    | ~ spl21_158 ),
    inference(resolution,[],[f1073,f188])).

fof(f1073,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK0)))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_158 ),
    inference(resolution,[],[f1071,f201])).

fof(f1071,plain,
    ( v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK0))))
    | ~ spl21_158 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f2018,plain,
    ( spl21_154
    | spl21_146
    | ~ spl21_158
    | ~ spl21_240 ),
    inference(avatar_split_clause,[],[f1873,f1630,f1070,f1002,f1039])).

fof(f1039,plain,
    ( spl21_154
  <=> v1_zfmisc_1(sK5(sK8(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_154])])).

fof(f1873,plain,
    ( v1_xboole_0(sK8(o_0_0_xboole_0))
    | v1_zfmisc_1(sK5(sK8(o_0_0_xboole_0)))
    | ~ spl21_158
    | ~ spl21_240 ),
    inference(forward_demodulation,[],[f1832,f1631])).

fof(f1832,plain,
    ( v1_zfmisc_1(sK5(sK8(o_0_0_xboole_0)))
    | v1_xboole_0(sK8(sK6(k1_zfmisc_1(sK0))))
    | ~ spl21_158
    | ~ spl21_240 ),
    inference(forward_demodulation,[],[f1822,f1631])).

fof(f1822,plain,
    ( v1_zfmisc_1(sK5(sK8(sK6(k1_zfmisc_1(sK0)))))
    | v1_xboole_0(sK8(sK6(k1_zfmisc_1(sK0))))
    | ~ spl21_158 ),
    inference(resolution,[],[f1073,f196])).

fof(f2017,plain,
    ( ~ spl21_287
    | ~ spl21_291
    | spl21_292
    | ~ spl21_284 ),
    inference(avatar_split_clause,[],[f1985,f1981,f2015,f2009,f1995])).

fof(f1995,plain,
    ( spl21_287
  <=> ~ v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_287])])).

fof(f2009,plain,
    ( spl21_291
  <=> ~ v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_291])])).

fof(f2015,plain,
    ( spl21_292
  <=> v1_funct_1(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_292])])).

fof(f1985,plain,
    ( v1_funct_1(k1_tarski(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl21_284 ),
    inference(resolution,[],[f1982,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc3_funct_1)).

fof(f2003,plain,
    ( ~ spl21_287
    | spl21_288
    | ~ spl21_284 ),
    inference(avatar_split_clause,[],[f1986,f1981,f2001,f1995])).

fof(f2001,plain,
    ( spl21_288
  <=> v1_relat_1(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_288])])).

fof(f1986,plain,
    ( v1_relat_1(k1_tarski(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl21_284 ),
    inference(resolution,[],[f1982,f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc2_relat_1)).

fof(f1983,plain,
    ( spl21_284
    | spl21_1
    | ~ spl21_52
    | ~ spl21_260 ),
    inference(avatar_split_clause,[],[f1934,f1805,f456,f274,f1981])).

fof(f274,plain,
    ( spl21_1
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_1])])).

fof(f456,plain,
    ( spl21_52
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_52])])).

fof(f1934,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl21_1
    | ~ spl21_52
    | ~ spl21_260 ),
    inference(forward_demodulation,[],[f1933,f1806])).

fof(f1933,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl21_1
    | ~ spl21_52 ),
    inference(subsumption_resolution,[],[f1923,f275])).

fof(f275,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl21_1 ),
    inference(avatar_component_clause,[],[f274])).

fof(f1923,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | ~ spl21_52 ),
    inference(resolution,[],[f237,f457])).

fof(f457,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl21_52 ),
    inference(avatar_component_clause,[],[f456])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',dt_k6_domain_1)).

fof(f1975,plain,
    ( spl21_280
    | spl21_282 ),
    inference(avatar_split_clause,[],[f1961,f1973,f1967])).

fof(f1967,plain,
    ( spl21_280
  <=> ! [X1] : ~ v1_relat_1(k1_zfmisc_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_280])])).

fof(f1973,plain,
    ( spl21_282
  <=> v1_relat_1(k1_tarski(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_282])])).

fof(f1961,plain,(
    ! [X1] :
      ( v1_relat_1(k1_tarski(o_0_0_xboole_0))
      | ~ v1_relat_1(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f1932,f202])).

fof(f1932,plain,(
    ! [X0] : m1_subset_1(k1_tarski(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(forward_demodulation,[],[f1931,f1792])).

fof(f1792,plain,(
    ! [X0] : k6_domain_1(k1_zfmisc_1(X0),o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f1783,f183])).

fof(f183,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',fc1_subset_1)).

fof(f1783,plain,(
    ! [X0] :
      ( k6_domain_1(k1_zfmisc_1(X0),o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f236,f485])).

fof(f485,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f229,f482])).

fof(f482,plain,(
    ! [X0] : o_0_0_xboole_0 = sK7(X0) ),
    inference(resolution,[],[f266,f230])).

fof(f230,plain,(
    ! [X0] : v1_xboole_0(sK7(X0)) ),
    inference(cnf_transformation,[],[f148])).

fof(f148,plain,(
    ! [X0] :
      ( v1_xboole_0(sK7(X0))
      & m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK7(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc2_subset_1)).

fof(f266,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f208,f181])).

fof(f181,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

fof(f50,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',d2_xboole_0)).

fof(f208,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',t6_boole)).

fof(f229,plain,(
    ! [X0] : m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f148])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',redefinition_k6_domain_1)).

fof(f1931,plain,(
    ! [X0] : m1_subset_1(k6_domain_1(k1_zfmisc_1(X0),o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(subsumption_resolution,[],[f1922,f183])).

fof(f1922,plain,(
    ! [X0] :
      ( m1_subset_1(k6_domain_1(k1_zfmisc_1(X0),o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f237,f485])).

fof(f1958,plain,
    ( spl21_278
    | ~ spl21_142 ),
    inference(avatar_split_clause,[],[f1394,f986,f1956])).

fof(f1956,plain,
    ( spl21_278
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK8(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_278])])).

fof(f986,plain,
    ( spl21_142
  <=> v1_zfmisc_1(sK8(sK8(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_142])])).

fof(f1394,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK8(o_0_0_xboole_0)))))
    | ~ spl21_142 ),
    inference(resolution,[],[f989,f228])).

fof(f989,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK8(o_0_0_xboole_0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_142 ),
    inference(resolution,[],[f987,f201])).

fof(f987,plain,
    ( v1_zfmisc_1(sK8(sK8(o_0_0_xboole_0)))
    | ~ spl21_142 ),
    inference(avatar_component_clause,[],[f986])).

fof(f1950,plain,
    ( spl21_276
    | ~ spl21_142 ),
    inference(avatar_split_clause,[],[f1396,f986,f1948])).

fof(f1948,plain,
    ( spl21_276
  <=> v1_zfmisc_1(sK8(sK8(sK8(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_276])])).

fof(f1396,plain,
    ( v1_zfmisc_1(sK8(sK8(sK8(o_0_0_xboole_0))))
    | ~ spl21_142 ),
    inference(resolution,[],[f989,f231])).

fof(f1920,plain,
    ( ~ spl21_4
    | spl21_117
    | spl21_275 ),
    inference(avatar_contradiction_clause,[],[f1919])).

fof(f1919,plain,
    ( $false
    | ~ spl21_4
    | ~ spl21_117
    | ~ spl21_275 ),
    inference(subsumption_resolution,[],[f1918,f839])).

fof(f839,plain,
    ( ~ v1_xboole_0(sK8(sK0))
    | ~ spl21_117 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl21_117
  <=> ~ v1_xboole_0(sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_117])])).

fof(f1918,plain,
    ( v1_xboole_0(sK8(sK0))
    | ~ spl21_4
    | ~ spl21_275 ),
    inference(resolution,[],[f1916,f1687])).

fof(f1687,plain,
    ( ! [X0] :
        ( v1_subset_1(o_0_0_xboole_0,X0)
        | v1_xboole_0(X0) )
    | ~ spl21_4 ),
    inference(subsumption_resolution,[],[f1683,f485])).

fof(f1683,plain,
    ( ! [X0] :
        ( v1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))
        | v1_xboole_0(X0) )
    | ~ spl21_4 ),
    inference(resolution,[],[f186,f289])).

fof(f289,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl21_4 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl21_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_4])])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_xboole_0(X1)
           => v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc3_subset_1)).

fof(f1916,plain,
    ( ~ v1_subset_1(o_0_0_xboole_0,sK8(sK0))
    | ~ spl21_275 ),
    inference(avatar_component_clause,[],[f1915])).

fof(f1915,plain,
    ( spl21_275
  <=> ~ v1_subset_1(o_0_0_xboole_0,sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_275])])).

fof(f1917,plain,
    ( ~ spl21_275
    | ~ spl21_268 ),
    inference(avatar_split_clause,[],[f1910,f1862,f1915])).

fof(f1862,plain,
    ( spl21_268
  <=> o_0_0_xboole_0 = sK8(sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_268])])).

fof(f1910,plain,
    ( ~ v1_subset_1(o_0_0_xboole_0,sK8(sK0))
    | ~ spl21_268 ),
    inference(superposition,[],[f232,f1863])).

fof(f1863,plain,
    ( o_0_0_xboole_0 = sK8(sK8(sK0))
    | ~ spl21_268 ),
    inference(avatar_component_clause,[],[f1862])).

fof(f232,plain,(
    ! [X0] : ~ v1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f150])).

fof(f1900,plain,
    ( spl21_272
    | ~ spl21_70 ),
    inference(avatar_split_clause,[],[f1604,f568,f1898])).

fof(f1898,plain,
    ( spl21_272
  <=> v4_funct_1(sK8(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_272])])).

fof(f568,plain,
    ( spl21_70
  <=> v4_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_70])])).

fof(f1604,plain,
    ( v4_funct_1(sK8(o_0_0_xboole_0))
    | ~ spl21_70 ),
    inference(resolution,[],[f571,f231])).

fof(f571,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | v4_funct_1(X0) )
    | ~ spl21_70 ),
    inference(resolution,[],[f569,f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v4_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v4_funct_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v4_funct_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v4_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc10_funct_1)).

fof(f569,plain,
    ( v4_funct_1(o_0_0_xboole_0)
    | ~ spl21_70 ),
    inference(avatar_component_clause,[],[f568])).

fof(f1892,plain,
    ( spl21_146
    | ~ spl21_4 ),
    inference(avatar_split_clause,[],[f1494,f288,f1002])).

fof(f1494,plain,
    ( v1_xboole_0(sK8(o_0_0_xboole_0))
    | ~ spl21_4 ),
    inference(resolution,[],[f892,f231])).

fof(f892,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl21_4 ),
    inference(resolution,[],[f209,f289])).

fof(f1890,plain,
    ( spl21_126
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(avatar_split_clause,[],[f1885,f1023,f1008,f889])).

fof(f889,plain,
    ( spl21_126
  <=> v1_zfmisc_1(sK2(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_126])])).

fof(f1885,plain,
    ( v1_zfmisc_1(sK2(o_0_0_xboole_0))
    | ~ spl21_148
    | ~ spl21_150 ),
    inference(superposition,[],[f1009,f1024])).

fof(f1877,plain,
    ( ~ spl21_4
    | spl21_147 ),
    inference(avatar_contradiction_clause,[],[f1876])).

fof(f1876,plain,
    ( $false
    | ~ spl21_4
    | ~ spl21_147 ),
    inference(subsumption_resolution,[],[f1000,f1494])).

fof(f1000,plain,
    ( ~ v1_xboole_0(sK8(o_0_0_xboole_0))
    | ~ spl21_147 ),
    inference(avatar_component_clause,[],[f999])).

fof(f999,plain,
    ( spl21_147
  <=> ~ v1_xboole_0(sK8(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_147])])).

fof(f1872,plain,
    ( spl21_264
    | spl21_270
    | ~ spl21_100 ),
    inference(avatar_split_clause,[],[f1086,f737,f1870,f1843])).

fof(f1843,plain,
    ( spl21_264
  <=> v1_xboole_0(sK8(sK8(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_264])])).

fof(f1870,plain,
    ( spl21_270
  <=> v1_zfmisc_1(sK5(sK8(sK8(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_270])])).

fof(f737,plain,
    ( spl21_100
  <=> v1_zfmisc_1(sK8(sK8(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_100])])).

fof(f1086,plain,
    ( v1_zfmisc_1(sK5(sK8(sK8(sK0))))
    | v1_xboole_0(sK8(sK8(sK0)))
    | ~ spl21_100 ),
    inference(resolution,[],[f740,f196])).

fof(f740,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK8(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_100 ),
    inference(resolution,[],[f738,f201])).

fof(f738,plain,
    ( v1_zfmisc_1(sK8(sK8(sK0)))
    | ~ spl21_100 ),
    inference(avatar_component_clause,[],[f737])).

fof(f1864,plain,
    ( spl21_268
    | ~ spl21_264 ),
    inference(avatar_split_clause,[],[f1857,f1843,f1862])).

fof(f1857,plain,
    ( o_0_0_xboole_0 = sK8(sK8(sK0))
    | ~ spl21_264 ),
    inference(resolution,[],[f1844,f266])).

fof(f1844,plain,
    ( v1_xboole_0(sK8(sK8(sK0)))
    | ~ spl21_264 ),
    inference(avatar_component_clause,[],[f1843])).

fof(f1851,plain,
    ( spl21_264
    | spl21_266
    | ~ spl21_100 ),
    inference(avatar_split_clause,[],[f1083,f737,f1849,f1843])).

fof(f1849,plain,
    ( spl21_266
  <=> v1_zfmisc_1(sK2(sK8(sK8(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_266])])).

fof(f1083,plain,
    ( v1_zfmisc_1(sK2(sK8(sK8(sK0))))
    | v1_xboole_0(sK8(sK8(sK0)))
    | ~ spl21_100 ),
    inference(resolution,[],[f740,f188])).

fof(f1815,plain,
    ( spl21_262
    | ~ spl21_56
    | ~ spl21_260 ),
    inference(avatar_split_clause,[],[f1808,f1805,f470,f1813])).

fof(f1808,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl21_56
    | ~ spl21_260 ),
    inference(superposition,[],[f471,f1806])).

fof(f1807,plain,
    ( spl21_260
    | spl21_1
    | ~ spl21_52 ),
    inference(avatar_split_clause,[],[f1793,f456,f274,f1805])).

fof(f1793,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl21_1
    | ~ spl21_52 ),
    inference(subsumption_resolution,[],[f1784,f275])).

fof(f1784,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0)
    | ~ spl21_52 ),
    inference(resolution,[],[f236,f457])).

fof(f1782,plain,
    ( spl21_258
    | ~ spl21_114 ),
    inference(avatar_split_clause,[],[f1764,f833,f1780])).

fof(f1780,plain,
    ( spl21_258
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_258])])).

fof(f833,plain,
    ( spl21_114
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_114])])).

fof(f1764,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK0))))))
    | ~ spl21_114 ),
    inference(resolution,[],[f836,f228])).

fof(f836,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK0)))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_114 ),
    inference(resolution,[],[f834,f201])).

fof(f834,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK0))))
    | ~ spl21_114 ),
    inference(avatar_component_clause,[],[f833])).

fof(f1774,plain,
    ( spl21_256
    | ~ spl21_114 ),
    inference(avatar_split_clause,[],[f1766,f833,f1772])).

fof(f1772,plain,
    ( spl21_256
  <=> v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_256])])).

fof(f1766,plain,
    ( v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK5(sK0)))))
    | ~ spl21_114 ),
    inference(resolution,[],[f836,f231])).

fof(f1757,plain,
    ( spl21_254
    | ~ spl21_120 ),
    inference(avatar_split_clause,[],[f1739,f855,f1755])).

fof(f1755,plain,
    ( spl21_254
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK8(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_254])])).

fof(f855,plain,
    ( spl21_120
  <=> v1_zfmisc_1(sK5(sK8(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_120])])).

fof(f1739,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK8(sK0)))))
    | ~ spl21_120 ),
    inference(resolution,[],[f1698,f228])).

fof(f1698,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK8(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_120 ),
    inference(resolution,[],[f856,f201])).

fof(f856,plain,
    ( v1_zfmisc_1(sK5(sK8(sK0)))
    | ~ spl21_120 ),
    inference(avatar_component_clause,[],[f855])).

fof(f1749,plain,
    ( spl21_252
    | ~ spl21_120 ),
    inference(avatar_split_clause,[],[f1741,f855,f1747])).

fof(f1747,plain,
    ( spl21_252
  <=> v1_zfmisc_1(sK8(sK5(sK8(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_252])])).

fof(f1741,plain,
    ( v1_zfmisc_1(sK8(sK5(sK8(sK0))))
    | ~ spl21_120 ),
    inference(resolution,[],[f1698,f231])).

fof(f1722,plain,
    ( spl21_250
    | ~ spl21_110 ),
    inference(avatar_split_clause,[],[f1672,f808,f1720])).

fof(f1720,plain,
    ( spl21_250
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_250])])).

fof(f808,plain,
    ( spl21_110
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_110])])).

fof(f1672,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK0))))))
    | ~ spl21_110 ),
    inference(resolution,[],[f811,f228])).

fof(f811,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK0)))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_110 ),
    inference(resolution,[],[f809,f201])).

fof(f809,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK0))))
    | ~ spl21_110 ),
    inference(avatar_component_clause,[],[f808])).

fof(f1715,plain,
    ( spl21_248
    | ~ spl21_102 ),
    inference(avatar_split_clause,[],[f1653,f745,f1713])).

fof(f1713,plain,
    ( spl21_248
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_248])])).

fof(f745,plain,
    ( spl21_102
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_102])])).

fof(f1653,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK0))))))
    | ~ spl21_102 ),
    inference(resolution,[],[f748,f228])).

fof(f748,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK0)))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_102 ),
    inference(resolution,[],[f746,f201])).

fof(f746,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK0))))
    | ~ spl21_102 ),
    inference(avatar_component_clause,[],[f745])).

fof(f1707,plain,
    ( spl21_246
    | ~ spl21_102 ),
    inference(avatar_split_clause,[],[f1655,f745,f1705])).

fof(f1705,plain,
    ( spl21_246
  <=> v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK8(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_246])])).

fof(f1655,plain,
    ( v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK8(sK0)))))
    | ~ spl21_102 ),
    inference(resolution,[],[f748,f231])).

fof(f1696,plain,
    ( spl21_1
    | ~ spl21_4
    | spl21_125 ),
    inference(avatar_contradiction_clause,[],[f1695])).

fof(f1695,plain,
    ( $false
    | ~ spl21_1
    | ~ spl21_4
    | ~ spl21_125 ),
    inference(subsumption_resolution,[],[f1693,f275])).

fof(f1693,plain,
    ( v1_xboole_0(sK0)
    | ~ spl21_4
    | ~ spl21_125 ),
    inference(resolution,[],[f1687,f883])).

fof(f883,plain,
    ( ~ v1_subset_1(o_0_0_xboole_0,sK0)
    | ~ spl21_125 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl21_125
  <=> ~ v1_subset_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_125])])).

fof(f1682,plain,
    ( spl21_244
    | ~ spl21_110 ),
    inference(avatar_split_clause,[],[f1674,f808,f1680])).

fof(f1680,plain,
    ( spl21_244
  <=> v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_244])])).

fof(f1674,plain,
    ( v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK2(sK0)))))
    | ~ spl21_110 ),
    inference(resolution,[],[f811,f231])).

fof(f1640,plain,
    ( spl21_236
    | spl21_242
    | ~ spl21_90 ),
    inference(avatar_split_clause,[],[f1061,f679,f1638,f1612])).

fof(f1612,plain,
    ( spl21_236
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_236])])).

fof(f1638,plain,
    ( spl21_242
  <=> v1_zfmisc_1(sK5(sK6(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_242])])).

fof(f679,plain,
    ( spl21_90
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_90])])).

fof(f1061,plain,
    ( v1_zfmisc_1(sK5(sK6(k1_zfmisc_1(sK0))))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK0)))
    | ~ spl21_90 ),
    inference(resolution,[],[f698,f196])).

fof(f698,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_90 ),
    inference(resolution,[],[f680,f201])).

fof(f680,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK0)))
    | ~ spl21_90 ),
    inference(avatar_component_clause,[],[f679])).

fof(f1632,plain,
    ( spl21_240
    | ~ spl21_236 ),
    inference(avatar_split_clause,[],[f1625,f1612,f1630])).

fof(f1625,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK0))
    | ~ spl21_236 ),
    inference(resolution,[],[f1613,f266])).

fof(f1613,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK0)))
    | ~ spl21_236 ),
    inference(avatar_component_clause,[],[f1612])).

fof(f1620,plain,
    ( spl21_236
    | spl21_238
    | ~ spl21_90 ),
    inference(avatar_split_clause,[],[f1058,f679,f1618,f1612])).

fof(f1618,plain,
    ( spl21_238
  <=> v1_zfmisc_1(sK2(sK6(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_238])])).

fof(f1058,plain,
    ( v1_zfmisc_1(sK2(sK6(k1_zfmisc_1(sK0))))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK0)))
    | ~ spl21_90 ),
    inference(resolution,[],[f698,f188])).

fof(f1596,plain,
    ( spl21_234
    | ~ spl21_82 ),
    inference(avatar_split_clause,[],[f1589,f625,f1594])).

fof(f1594,plain,
    ( spl21_234
  <=> v1_relat_1(sK6(sK5(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_234])])).

fof(f625,plain,
    ( spl21_82
  <=> v4_funct_1(sK5(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_82])])).

fof(f1589,plain,
    ( v1_relat_1(sK6(sK5(sK12)))
    | ~ spl21_82 ),
    inference(resolution,[],[f630,f228])).

fof(f630,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK5(sK12))
        | v1_relat_1(X2) )
    | ~ spl21_82 ),
    inference(resolution,[],[f626,f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
          | ~ m1_subset_1(X1,X0) )
      | ~ v4_funct_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v4_funct_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ( v1_funct_1(X1)
            & v1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc9_funct_1)).

fof(f626,plain,
    ( v4_funct_1(sK5(sK12))
    | ~ spl21_82 ),
    inference(avatar_component_clause,[],[f625])).

fof(f1588,plain,
    ( spl21_232
    | ~ spl21_82 ),
    inference(avatar_split_clause,[],[f1581,f625,f1586])).

fof(f1586,plain,
    ( spl21_232
  <=> v1_funct_1(sK6(sK5(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_232])])).

fof(f1581,plain,
    ( v1_funct_1(sK6(sK5(sK12)))
    | ~ spl21_82 ),
    inference(resolution,[],[f629,f228])).

fof(f629,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK5(sK12))
        | v1_funct_1(X1) )
    | ~ spl21_82 ),
    inference(resolution,[],[f626,f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f1580,plain,
    ( spl21_230
    | ~ spl21_80 ),
    inference(avatar_split_clause,[],[f1573,f615,f1578])).

fof(f1578,plain,
    ( spl21_230
  <=> v1_relat_1(sK6(sK4(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_230])])).

fof(f615,plain,
    ( spl21_80
  <=> v4_funct_1(sK4(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_80])])).

fof(f1573,plain,
    ( v1_relat_1(sK6(sK4(sK12)))
    | ~ spl21_80 ),
    inference(resolution,[],[f620,f228])).

fof(f620,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK12))
        | v1_relat_1(X2) )
    | ~ spl21_80 ),
    inference(resolution,[],[f616,f198])).

fof(f616,plain,
    ( v4_funct_1(sK4(sK12))
    | ~ spl21_80 ),
    inference(avatar_component_clause,[],[f615])).

fof(f1572,plain,
    ( spl21_228
    | ~ spl21_80 ),
    inference(avatar_split_clause,[],[f1565,f615,f1570])).

fof(f1570,plain,
    ( spl21_228
  <=> v1_funct_1(sK6(sK4(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_228])])).

fof(f1565,plain,
    ( v1_funct_1(sK6(sK4(sK12)))
    | ~ spl21_80 ),
    inference(resolution,[],[f619,f228])).

fof(f619,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK12))
        | v1_funct_1(X1) )
    | ~ spl21_80 ),
    inference(resolution,[],[f616,f199])).

fof(f1563,plain,
    ( spl21_226
    | ~ spl21_78 ),
    inference(avatar_split_clause,[],[f1556,f605,f1561])).

fof(f1561,plain,
    ( spl21_226
  <=> v1_relat_1(sK6(sK3(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_226])])).

fof(f605,plain,
    ( spl21_78
  <=> v4_funct_1(sK3(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_78])])).

fof(f1556,plain,
    ( v1_relat_1(sK6(sK3(sK12)))
    | ~ spl21_78 ),
    inference(resolution,[],[f610,f228])).

fof(f610,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK12))
        | v1_relat_1(X2) )
    | ~ spl21_78 ),
    inference(resolution,[],[f606,f198])).

fof(f606,plain,
    ( v4_funct_1(sK3(sK12))
    | ~ spl21_78 ),
    inference(avatar_component_clause,[],[f605])).

fof(f1555,plain,
    ( spl21_224
    | ~ spl21_78 ),
    inference(avatar_split_clause,[],[f1548,f605,f1553])).

fof(f1553,plain,
    ( spl21_224
  <=> v1_funct_1(sK6(sK3(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_224])])).

fof(f1548,plain,
    ( v1_funct_1(sK6(sK3(sK12)))
    | ~ spl21_78 ),
    inference(resolution,[],[f609,f228])).

fof(f609,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK12))
        | v1_funct_1(X1) )
    | ~ spl21_78 ),
    inference(resolution,[],[f606,f199])).

fof(f1547,plain,
    ( spl21_222
    | ~ spl21_76 ),
    inference(avatar_split_clause,[],[f1540,f595,f1545])).

fof(f1545,plain,
    ( spl21_222
  <=> v1_relat_1(sK6(sK2(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_222])])).

fof(f595,plain,
    ( spl21_76
  <=> v4_funct_1(sK2(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_76])])).

fof(f1540,plain,
    ( v1_relat_1(sK6(sK2(sK12)))
    | ~ spl21_76 ),
    inference(resolution,[],[f600,f228])).

fof(f600,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK12))
        | v1_relat_1(X2) )
    | ~ spl21_76 ),
    inference(resolution,[],[f596,f198])).

fof(f596,plain,
    ( v4_funct_1(sK2(sK12))
    | ~ spl21_76 ),
    inference(avatar_component_clause,[],[f595])).

fof(f1539,plain,
    ( spl21_220
    | ~ spl21_76 ),
    inference(avatar_split_clause,[],[f1532,f595,f1537])).

fof(f1537,plain,
    ( spl21_220
  <=> v1_funct_1(sK6(sK2(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_220])])).

fof(f1532,plain,
    ( v1_funct_1(sK6(sK2(sK12)))
    | ~ spl21_76 ),
    inference(resolution,[],[f599,f228])).

fof(f599,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK12))
        | v1_funct_1(X1) )
    | ~ spl21_76 ),
    inference(resolution,[],[f596,f199])).

fof(f1531,plain,
    ( spl21_218
    | ~ spl21_72 ),
    inference(avatar_split_clause,[],[f1524,f578,f1529])).

fof(f1529,plain,
    ( spl21_218
  <=> v1_relat_1(sK6(sK8(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_218])])).

fof(f578,plain,
    ( spl21_72
  <=> v4_funct_1(sK8(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_72])])).

fof(f1524,plain,
    ( v1_relat_1(sK6(sK8(sK12)))
    | ~ spl21_72 ),
    inference(resolution,[],[f583,f228])).

fof(f583,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK8(sK12))
        | v1_relat_1(X2) )
    | ~ spl21_72 ),
    inference(resolution,[],[f579,f198])).

fof(f579,plain,
    ( v4_funct_1(sK8(sK12))
    | ~ spl21_72 ),
    inference(avatar_component_clause,[],[f578])).

fof(f1514,plain,
    ( spl21_216
    | ~ spl21_214 ),
    inference(avatar_split_clause,[],[f1507,f1500,f1512])).

fof(f1512,plain,
    ( spl21_216
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_216])])).

fof(f1500,plain,
    ( spl21_214
  <=> v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_214])])).

fof(f1507,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl21_214 ),
    inference(resolution,[],[f1501,f266])).

fof(f1501,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl21_214 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f1502,plain,
    ( spl21_214
    | ~ spl21_4 ),
    inference(avatar_split_clause,[],[f1492,f288,f1500])).

fof(f1492,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl21_4 ),
    inference(resolution,[],[f892,f228])).

fof(f1486,plain,
    ( spl21_210
    | spl21_212 ),
    inference(avatar_split_clause,[],[f1468,f1484,f1478])).

fof(f1478,plain,
    ( spl21_210
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_210])])).

fof(f1484,plain,
    ( spl21_212
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_212])])).

fof(f1468,plain,(
    ! [X0] :
      ( v1_funct_1(o_0_0_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f220,f485])).

fof(f1465,plain,
    ( spl21_208
    | spl21_19
    | ~ spl21_20 ),
    inference(avatar_split_clause,[],[f1434,f344,f337,f1463])).

fof(f1463,plain,
    ( spl21_208
  <=> v1_zfmisc_1(sK5(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_208])])).

fof(f337,plain,
    ( spl21_19
  <=> ~ v1_xboole_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_19])])).

fof(f344,plain,
    ( spl21_20
  <=> v1_zfmisc_1(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_20])])).

fof(f1434,plain,
    ( v1_zfmisc_1(sK5(sK13))
    | ~ spl21_19
    | ~ spl21_20 ),
    inference(subsumption_resolution,[],[f1429,f338])).

fof(f338,plain,
    ( ~ v1_xboole_0(sK13)
    | ~ spl21_19 ),
    inference(avatar_component_clause,[],[f337])).

fof(f1429,plain,
    ( v1_zfmisc_1(sK5(sK13))
    | v1_xboole_0(sK13)
    | ~ spl21_20 ),
    inference(resolution,[],[f640,f196])).

fof(f640,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(sK13))
        | v1_zfmisc_1(X9) )
    | ~ spl21_20 ),
    inference(resolution,[],[f201,f345])).

fof(f345,plain,
    ( v1_zfmisc_1(sK13)
    | ~ spl21_20 ),
    inference(avatar_component_clause,[],[f344])).

fof(f1457,plain,
    ( spl21_206
    | spl21_19
    | ~ spl21_20 ),
    inference(avatar_split_clause,[],[f1433,f344,f337,f1455])).

fof(f1455,plain,
    ( spl21_206
  <=> v1_zfmisc_1(sK2(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_206])])).

fof(f1433,plain,
    ( v1_zfmisc_1(sK2(sK13))
    | ~ spl21_19
    | ~ spl21_20 ),
    inference(subsumption_resolution,[],[f1426,f338])).

fof(f1426,plain,
    ( v1_zfmisc_1(sK2(sK13))
    | v1_xboole_0(sK13)
    | ~ spl21_20 ),
    inference(resolution,[],[f640,f188])).

fof(f1450,plain,
    ( spl21_204
    | ~ spl21_20 ),
    inference(avatar_split_clause,[],[f1430,f344,f1448])).

fof(f1448,plain,
    ( spl21_204
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_204])])).

fof(f1430,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK13)))
    | ~ spl21_20 ),
    inference(resolution,[],[f640,f228])).

fof(f1442,plain,
    ( spl21_202
    | ~ spl21_20 ),
    inference(avatar_split_clause,[],[f1432,f344,f1440])).

fof(f1440,plain,
    ( spl21_202
  <=> v1_zfmisc_1(sK8(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_202])])).

fof(f1432,plain,
    ( v1_zfmisc_1(sK8(sK13))
    | ~ spl21_20 ),
    inference(resolution,[],[f640,f231])).

fof(f1387,plain,
    ( spl21_200
    | ~ spl21_98 ),
    inference(avatar_split_clause,[],[f1369,f720,f1385])).

fof(f1385,plain,
    ( spl21_200
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_200])])).

fof(f720,plain,
    ( spl21_98
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_98])])).

fof(f1369,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl21_98 ),
    inference(resolution,[],[f723,f228])).

fof(f723,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_98 ),
    inference(resolution,[],[f721,f201])).

fof(f721,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl21_98 ),
    inference(avatar_component_clause,[],[f720])).

fof(f1379,plain,
    ( spl21_198
    | ~ spl21_98 ),
    inference(avatar_split_clause,[],[f1371,f720,f1377])).

fof(f1377,plain,
    ( spl21_198
  <=> v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_198])])).

fof(f1371,plain,
    ( v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl21_98 ),
    inference(resolution,[],[f723,f231])).

fof(f1362,plain,
    ( spl21_196
    | ~ spl21_140 ),
    inference(avatar_split_clause,[],[f1343,f958,f1360])).

fof(f1360,plain,
    ( spl21_196
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_196])])).

fof(f958,plain,
    ( spl21_140
  <=> v1_zfmisc_1(sK5(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_140])])).

fof(f1343,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK5(sK0)))))
    | ~ spl21_140 ),
    inference(resolution,[],[f1299,f228])).

fof(f1299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK5(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_140 ),
    inference(resolution,[],[f959,f201])).

fof(f959,plain,
    ( v1_zfmisc_1(sK5(sK5(sK0)))
    | ~ spl21_140 ),
    inference(avatar_component_clause,[],[f958])).

fof(f1353,plain,
    ( spl21_194
    | ~ spl21_140 ),
    inference(avatar_split_clause,[],[f1345,f958,f1351])).

fof(f1351,plain,
    ( spl21_194
  <=> v1_zfmisc_1(sK8(sK5(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_194])])).

fof(f1345,plain,
    ( v1_zfmisc_1(sK8(sK5(sK5(sK0))))
    | ~ spl21_140 ),
    inference(resolution,[],[f1299,f231])).

fof(f1316,plain,
    ( spl21_192
    | ~ spl21_118 ),
    inference(avatar_split_clause,[],[f1306,f847,f1314])).

fof(f1314,plain,
    ( spl21_192
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK8(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_192])])).

fof(f847,plain,
    ( spl21_118
  <=> v1_zfmisc_1(sK2(sK8(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_118])])).

fof(f1306,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK8(sK0)))))
    | ~ spl21_118 ),
    inference(resolution,[],[f1275,f228])).

fof(f1275,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK8(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_118 ),
    inference(resolution,[],[f848,f201])).

fof(f848,plain,
    ( v1_zfmisc_1(sK2(sK8(sK0)))
    | ~ spl21_118 ),
    inference(avatar_component_clause,[],[f847])).

fof(f1297,plain,
    ( spl21_190
    | ~ spl21_138
    | ~ spl21_186 ),
    inference(avatar_split_clause,[],[f1284,f1260,f950,f1295])).

fof(f950,plain,
    ( spl21_138
  <=> o_0_0_xboole_0 = sK5(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_138])])).

fof(f1260,plain,
    ( spl21_186
  <=> v1_zfmisc_1(sK8(sK2(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_186])])).

fof(f1284,plain,
    ( v1_zfmisc_1(sK8(sK2(o_0_0_xboole_0)))
    | ~ spl21_138
    | ~ spl21_186 ),
    inference(superposition,[],[f1261,f951])).

fof(f951,plain,
    ( o_0_0_xboole_0 = sK5(sK0)
    | ~ spl21_138 ),
    inference(avatar_component_clause,[],[f950])).

fof(f1261,plain,
    ( v1_zfmisc_1(sK8(sK2(sK5(sK0))))
    | ~ spl21_186 ),
    inference(avatar_component_clause,[],[f1260])).

fof(f1288,plain,
    ( spl21_124
    | spl21_1
    | ~ spl21_138 ),
    inference(avatar_split_clause,[],[f1287,f950,f274,f879])).

fof(f879,plain,
    ( spl21_124
  <=> v1_subset_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_124])])).

fof(f1287,plain,
    ( v1_subset_1(o_0_0_xboole_0,sK0)
    | ~ spl21_1
    | ~ spl21_138 ),
    inference(subsumption_resolution,[],[f1286,f275])).

fof(f1286,plain,
    ( v1_subset_1(o_0_0_xboole_0,sK0)
    | v1_xboole_0(sK0)
    | ~ spl21_138 ),
    inference(superposition,[],[f197,f951])).

fof(f197,plain,(
    ! [X0] :
      ( v1_subset_1(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f1272,plain,
    ( spl21_188
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f1252,f938,f1270])).

fof(f1270,plain,
    ( spl21_188
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_188])])).

fof(f938,plain,
    ( spl21_136
  <=> v1_zfmisc_1(sK2(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_136])])).

fof(f1252,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK5(sK0)))))
    | ~ spl21_136 ),
    inference(resolution,[],[f971,f228])).

fof(f971,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK5(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_136 ),
    inference(resolution,[],[f939,f201])).

fof(f939,plain,
    ( v1_zfmisc_1(sK2(sK5(sK0)))
    | ~ spl21_136 ),
    inference(avatar_component_clause,[],[f938])).

fof(f1262,plain,
    ( spl21_186
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f1254,f938,f1260])).

fof(f1254,plain,
    ( v1_zfmisc_1(sK8(sK2(sK5(sK0))))
    | ~ spl21_136 ),
    inference(resolution,[],[f971,f231])).

fof(f1245,plain,
    ( spl21_184
    | ~ spl21_132 ),
    inference(avatar_split_clause,[],[f1227,f924,f1243])).

fof(f1243,plain,
    ( spl21_184
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_184])])).

fof(f924,plain,
    ( spl21_132
  <=> v1_zfmisc_1(sK5(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_132])])).

fof(f1227,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK2(sK0)))))
    | ~ spl21_132 ),
    inference(resolution,[],[f927,f228])).

fof(f927,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK2(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_132 ),
    inference(resolution,[],[f925,f201])).

fof(f925,plain,
    ( v1_zfmisc_1(sK5(sK2(sK0)))
    | ~ spl21_132 ),
    inference(avatar_component_clause,[],[f924])).

fof(f1237,plain,
    ( spl21_182
    | ~ spl21_132 ),
    inference(avatar_split_clause,[],[f1229,f924,f1235])).

fof(f1235,plain,
    ( spl21_182
  <=> v1_zfmisc_1(sK8(sK5(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_182])])).

fof(f1229,plain,
    ( v1_zfmisc_1(sK8(sK5(sK2(sK0))))
    | ~ spl21_132 ),
    inference(resolution,[],[f927,f231])).

fof(f1220,plain,
    ( spl21_180
    | ~ spl21_130 ),
    inference(avatar_split_clause,[],[f1202,f908,f1218])).

fof(f1218,plain,
    ( spl21_180
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_180])])).

fof(f908,plain,
    ( spl21_130
  <=> v1_zfmisc_1(sK2(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_130])])).

fof(f1202,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK2(sK0)))))
    | ~ spl21_130 ),
    inference(resolution,[],[f919,f228])).

fof(f919,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK2(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_130 ),
    inference(resolution,[],[f909,f201])).

fof(f909,plain,
    ( v1_zfmisc_1(sK2(sK2(sK0)))
    | ~ spl21_130 ),
    inference(avatar_component_clause,[],[f908])).

fof(f1212,plain,
    ( spl21_178
    | ~ spl21_130 ),
    inference(avatar_split_clause,[],[f1204,f908,f1210])).

fof(f1210,plain,
    ( spl21_178
  <=> v1_zfmisc_1(sK8(sK2(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_178])])).

fof(f1204,plain,
    ( v1_zfmisc_1(sK8(sK2(sK2(sK0))))
    | ~ spl21_130 ),
    inference(resolution,[],[f919,f231])).

fof(f1186,plain,
    ( ~ spl21_177
    | spl21_127 ),
    inference(avatar_split_clause,[],[f1179,f886,f1184])).

fof(f886,plain,
    ( spl21_127
  <=> ~ v1_zfmisc_1(sK2(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_127])])).

fof(f1179,plain,
    ( ~ v1_xboole_0(sK2(o_0_0_xboole_0))
    | ~ spl21_127 ),
    inference(resolution,[],[f887,f185])).

fof(f185,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
     => ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc1_realset1)).

fof(f887,plain,
    ( ~ v1_zfmisc_1(sK2(o_0_0_xboole_0))
    | ~ spl21_127 ),
    inference(avatar_component_clause,[],[f886])).

fof(f1178,plain,
    ( ~ spl21_127
    | spl21_119
    | ~ spl21_122 ),
    inference(avatar_split_clause,[],[f1176,f866,f844,f886])).

fof(f844,plain,
    ( spl21_119
  <=> ~ v1_zfmisc_1(sK2(sK8(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_119])])).

fof(f866,plain,
    ( spl21_122
  <=> o_0_0_xboole_0 = sK8(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_122])])).

fof(f1176,plain,
    ( ~ v1_zfmisc_1(sK2(o_0_0_xboole_0))
    | ~ spl21_119
    | ~ spl21_122 ),
    inference(forward_demodulation,[],[f845,f867])).

fof(f867,plain,
    ( o_0_0_xboole_0 = sK8(sK0)
    | ~ spl21_122 ),
    inference(avatar_component_clause,[],[f866])).

fof(f845,plain,
    ( ~ v1_zfmisc_1(sK2(sK8(sK0)))
    | ~ spl21_119 ),
    inference(avatar_component_clause,[],[f844])).

fof(f1175,plain,
    ( spl21_174
    | ~ spl21_118 ),
    inference(avatar_split_clause,[],[f1167,f847,f1173])).

fof(f1173,plain,
    ( spl21_174
  <=> v1_zfmisc_1(sK8(sK2(sK8(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_174])])).

fof(f1167,plain,
    ( v1_zfmisc_1(sK8(sK2(sK8(sK0))))
    | ~ spl21_118 ),
    inference(resolution,[],[f850,f231])).

fof(f850,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK8(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_118 ),
    inference(resolution,[],[f848,f201])).

fof(f1158,plain,
    ( spl21_172
    | ~ spl21_112 ),
    inference(avatar_split_clause,[],[f1140,f825,f1156])).

fof(f1156,plain,
    ( spl21_172
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_172])])).

fof(f825,plain,
    ( spl21_112
  <=> v1_zfmisc_1(sK8(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_112])])).

fof(f1140,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK5(sK0)))))
    | ~ spl21_112 ),
    inference(resolution,[],[f828,f228])).

fof(f828,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK5(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_112 ),
    inference(resolution,[],[f826,f201])).

fof(f826,plain,
    ( v1_zfmisc_1(sK8(sK5(sK0)))
    | ~ spl21_112 ),
    inference(avatar_component_clause,[],[f825])).

fof(f1150,plain,
    ( spl21_170
    | ~ spl21_112 ),
    inference(avatar_split_clause,[],[f1142,f825,f1148])).

fof(f1148,plain,
    ( spl21_170
  <=> v1_zfmisc_1(sK8(sK8(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_170])])).

fof(f1142,plain,
    ( v1_zfmisc_1(sK8(sK8(sK5(sK0))))
    | ~ spl21_112 ),
    inference(resolution,[],[f828,f231])).

fof(f1130,plain,
    ( spl21_168
    | ~ spl21_104 ),
    inference(avatar_split_clause,[],[f1112,f771,f1128])).

fof(f1128,plain,
    ( spl21_168
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_168])])).

fof(f771,plain,
    ( spl21_104
  <=> v1_zfmisc_1(sK8(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_104])])).

fof(f1112,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK2(sK0)))))
    | ~ spl21_104 ),
    inference(resolution,[],[f774,f228])).

fof(f774,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK2(sK0))))
        | v1_zfmisc_1(X0) )
    | ~ spl21_104 ),
    inference(resolution,[],[f772,f201])).

fof(f772,plain,
    ( v1_zfmisc_1(sK8(sK2(sK0)))
    | ~ spl21_104 ),
    inference(avatar_component_clause,[],[f771])).

fof(f1122,plain,
    ( spl21_166
    | ~ spl21_104 ),
    inference(avatar_split_clause,[],[f1114,f771,f1120])).

fof(f1120,plain,
    ( spl21_166
  <=> v1_zfmisc_1(sK8(sK8(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_166])])).

fof(f1114,plain,
    ( v1_zfmisc_1(sK8(sK8(sK2(sK0))))
    | ~ spl21_104 ),
    inference(resolution,[],[f774,f231])).

fof(f1105,plain,
    ( spl21_164
    | ~ spl21_100 ),
    inference(avatar_split_clause,[],[f1087,f737,f1103])).

fof(f1103,plain,
    ( spl21_164
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK8(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_164])])).

fof(f1087,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK8(sK0)))))
    | ~ spl21_100 ),
    inference(resolution,[],[f740,f228])).

fof(f1097,plain,
    ( spl21_162
    | ~ spl21_100 ),
    inference(avatar_split_clause,[],[f1089,f737,f1095])).

fof(f1095,plain,
    ( spl21_162
  <=> v1_zfmisc_1(sK8(sK8(sK8(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_162])])).

fof(f1089,plain,
    ( v1_zfmisc_1(sK8(sK8(sK8(sK0))))
    | ~ spl21_100 ),
    inference(resolution,[],[f740,f231])).

fof(f1080,plain,
    ( spl21_160
    | ~ spl21_90 ),
    inference(avatar_split_clause,[],[f1062,f679,f1078])).

fof(f1078,plain,
    ( spl21_160
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_160])])).

fof(f1062,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK0)))))
    | ~ spl21_90 ),
    inference(resolution,[],[f698,f228])).

fof(f1072,plain,
    ( spl21_158
    | ~ spl21_90 ),
    inference(avatar_split_clause,[],[f1064,f679,f1070])).

fof(f1064,plain,
    ( v1_zfmisc_1(sK8(sK6(k1_zfmisc_1(sK0))))
    | ~ spl21_90 ),
    inference(resolution,[],[f698,f231])).

fof(f1056,plain,
    ( ~ spl21_157
    | ~ spl21_150 ),
    inference(avatar_split_clause,[],[f1049,f1023,f1054])).

fof(f1054,plain,
    ( spl21_157
  <=> ~ v1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_157])])).

fof(f1049,plain,
    ( ~ v1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl21_150 ),
    inference(superposition,[],[f232,f1024])).

fof(f1041,plain,
    ( spl21_146
    | spl21_154
    | ~ spl21_96 ),
    inference(avatar_split_clause,[],[f977,f712,f1039,f1002])).

fof(f712,plain,
    ( spl21_96
  <=> v1_zfmisc_1(sK8(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_96])])).

fof(f977,plain,
    ( v1_zfmisc_1(sK5(sK8(o_0_0_xboole_0)))
    | v1_xboole_0(sK8(o_0_0_xboole_0))
    | ~ spl21_96 ),
    inference(resolution,[],[f715,f196])).

fof(f715,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(o_0_0_xboole_0)))
        | v1_zfmisc_1(X0) )
    | ~ spl21_96 ),
    inference(resolution,[],[f713,f201])).

fof(f713,plain,
    ( v1_zfmisc_1(sK8(o_0_0_xboole_0))
    | ~ spl21_96 ),
    inference(avatar_component_clause,[],[f712])).

fof(f1033,plain,
    ( ~ spl21_153
    | ~ spl21_42
    | ~ spl21_44
    | spl21_47 ),
    inference(avatar_split_clause,[],[f1018,f435,f428,f421,f1031])).

fof(f1031,plain,
    ( spl21_153
  <=> ~ v1_zfmisc_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_153])])).

fof(f421,plain,
    ( spl21_42
  <=> v1_relat_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_42])])).

fof(f428,plain,
    ( spl21_44
  <=> v1_funct_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_44])])).

fof(f435,plain,
    ( spl21_47
  <=> ~ v3_funct_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_47])])).

fof(f1018,plain,
    ( ~ v1_zfmisc_1(sK19)
    | ~ spl21_42
    | ~ spl21_44
    | ~ spl21_47 ),
    inference(subsumption_resolution,[],[f1017,f422])).

fof(f422,plain,
    ( v1_relat_1(sK19)
    | ~ spl21_42 ),
    inference(avatar_component_clause,[],[f421])).

fof(f1017,plain,
    ( ~ v1_relat_1(sK19)
    | ~ v1_zfmisc_1(sK19)
    | ~ spl21_44
    | ~ spl21_47 ),
    inference(subsumption_resolution,[],[f1016,f429])).

fof(f429,plain,
    ( v1_funct_1(sK19)
    | ~ spl21_44 ),
    inference(avatar_component_clause,[],[f428])).

fof(f1016,plain,
    ( ~ v1_funct_1(sK19)
    | ~ v1_relat_1(sK19)
    | ~ v1_zfmisc_1(sK19)
    | ~ spl21_47 ),
    inference(resolution,[],[f215,f436])).

fof(f436,plain,
    ( ~ v3_funct_1(sK19)
    | ~ spl21_47 ),
    inference(avatar_component_clause,[],[f435])).

fof(f215,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_zfmisc_1(X0) )
     => ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc7_funct_1)).

fof(f1025,plain,
    ( spl21_150
    | ~ spl21_146 ),
    inference(avatar_split_clause,[],[f1015,f1002,f1023])).

fof(f1015,plain,
    ( o_0_0_xboole_0 = sK8(o_0_0_xboole_0)
    | ~ spl21_146 ),
    inference(resolution,[],[f1003,f266])).

fof(f1003,plain,
    ( v1_xboole_0(sK8(o_0_0_xboole_0))
    | ~ spl21_146 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f1010,plain,
    ( spl21_146
    | spl21_148
    | ~ spl21_96 ),
    inference(avatar_split_clause,[],[f974,f712,f1008,f1002])).

fof(f974,plain,
    ( v1_zfmisc_1(sK2(sK8(o_0_0_xboole_0)))
    | v1_xboole_0(sK8(o_0_0_xboole_0))
    | ~ spl21_96 ),
    inference(resolution,[],[f715,f188])).

fof(f996,plain,
    ( spl21_144
    | ~ spl21_96 ),
    inference(avatar_split_clause,[],[f978,f712,f994])).

fof(f994,plain,
    ( spl21_144
  <=> v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_144])])).

fof(f978,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(o_0_0_xboole_0))))
    | ~ spl21_96 ),
    inference(resolution,[],[f715,f228])).

fof(f988,plain,
    ( spl21_142
    | ~ spl21_96 ),
    inference(avatar_split_clause,[],[f980,f712,f986])).

fof(f980,plain,
    ( v1_zfmisc_1(sK8(sK8(o_0_0_xboole_0)))
    | ~ spl21_96 ),
    inference(resolution,[],[f715,f231])).

fof(f970,plain,
    ( spl21_1
    | spl21_125
    | ~ spl21_138 ),
    inference(avatar_contradiction_clause,[],[f969])).

fof(f969,plain,
    ( $false
    | ~ spl21_1
    | ~ spl21_125
    | ~ spl21_138 ),
    inference(subsumption_resolution,[],[f968,f275])).

fof(f968,plain,
    ( v1_xboole_0(sK0)
    | ~ spl21_125
    | ~ spl21_138 ),
    inference(subsumption_resolution,[],[f967,f883])).

fof(f967,plain,
    ( v1_subset_1(o_0_0_xboole_0,sK0)
    | v1_xboole_0(sK0)
    | ~ spl21_138 ),
    inference(superposition,[],[f197,f951])).

fof(f960,plain,
    ( spl21_134
    | spl21_140
    | ~ spl21_94 ),
    inference(avatar_split_clause,[],[f816,f694,f958,f932])).

fof(f932,plain,
    ( spl21_134
  <=> v1_xboole_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_134])])).

fof(f694,plain,
    ( spl21_94
  <=> v1_zfmisc_1(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_94])])).

fof(f816,plain,
    ( v1_zfmisc_1(sK5(sK5(sK0)))
    | v1_xboole_0(sK5(sK0))
    | ~ spl21_94 ),
    inference(resolution,[],[f697,f196])).

fof(f697,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK0)))
        | v1_zfmisc_1(X0) )
    | ~ spl21_94 ),
    inference(resolution,[],[f695,f201])).

fof(f695,plain,
    ( v1_zfmisc_1(sK5(sK0))
    | ~ spl21_94 ),
    inference(avatar_component_clause,[],[f694])).

fof(f952,plain,
    ( spl21_138
    | ~ spl21_134 ),
    inference(avatar_split_clause,[],[f945,f932,f950])).

fof(f945,plain,
    ( o_0_0_xboole_0 = sK5(sK0)
    | ~ spl21_134 ),
    inference(resolution,[],[f933,f266])).

fof(f933,plain,
    ( v1_xboole_0(sK5(sK0))
    | ~ spl21_134 ),
    inference(avatar_component_clause,[],[f932])).

fof(f940,plain,
    ( spl21_134
    | spl21_136
    | ~ spl21_94 ),
    inference(avatar_split_clause,[],[f813,f694,f938,f932])).

fof(f813,plain,
    ( v1_zfmisc_1(sK2(sK5(sK0)))
    | v1_xboole_0(sK5(sK0))
    | ~ spl21_94 ),
    inference(resolution,[],[f697,f188])).

fof(f926,plain,
    ( spl21_128
    | spl21_132
    | ~ spl21_92 ),
    inference(avatar_split_clause,[],[f753,f686,f924,f902])).

fof(f902,plain,
    ( spl21_128
  <=> v1_xboole_0(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_128])])).

fof(f686,plain,
    ( spl21_92
  <=> v1_zfmisc_1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_92])])).

fof(f753,plain,
    ( v1_zfmisc_1(sK5(sK2(sK0)))
    | v1_xboole_0(sK2(sK0))
    | ~ spl21_92 ),
    inference(resolution,[],[f689,f196])).

fof(f689,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK0)))
        | v1_zfmisc_1(X0) )
    | ~ spl21_92 ),
    inference(resolution,[],[f687,f201])).

fof(f687,plain,
    ( v1_zfmisc_1(sK2(sK0))
    | ~ spl21_92 ),
    inference(avatar_component_clause,[],[f686])).

fof(f918,plain,
    ( spl21_1
    | ~ spl21_128 ),
    inference(avatar_contradiction_clause,[],[f917])).

fof(f917,plain,
    ( $false
    | ~ spl21_1
    | ~ spl21_128 ),
    inference(subsumption_resolution,[],[f911,f275])).

fof(f911,plain,
    ( v1_xboole_0(sK0)
    | ~ spl21_128 ),
    inference(resolution,[],[f903,f189])).

fof(f189,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f903,plain,
    ( v1_xboole_0(sK2(sK0))
    | ~ spl21_128 ),
    inference(avatar_component_clause,[],[f902])).

fof(f910,plain,
    ( spl21_128
    | spl21_130
    | ~ spl21_92 ),
    inference(avatar_split_clause,[],[f750,f686,f908,f902])).

fof(f750,plain,
    ( v1_zfmisc_1(sK2(sK2(sK0)))
    | v1_xboole_0(sK2(sK0))
    | ~ spl21_92 ),
    inference(resolution,[],[f689,f188])).

fof(f891,plain,
    ( spl21_126
    | ~ spl21_118
    | ~ spl21_122 ),
    inference(avatar_split_clause,[],[f874,f866,f847,f889])).

fof(f874,plain,
    ( v1_zfmisc_1(sK2(o_0_0_xboole_0))
    | ~ spl21_118
    | ~ spl21_122 ),
    inference(superposition,[],[f848,f867])).

fof(f884,plain,
    ( ~ spl21_125
    | ~ spl21_122 ),
    inference(avatar_split_clause,[],[f877,f866,f882])).

fof(f877,plain,
    ( ~ v1_subset_1(o_0_0_xboole_0,sK0)
    | ~ spl21_122 ),
    inference(superposition,[],[f232,f867])).

fof(f868,plain,
    ( spl21_122
    | ~ spl21_116 ),
    inference(avatar_split_clause,[],[f861,f841,f866])).

fof(f841,plain,
    ( spl21_116
  <=> v1_xboole_0(sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_116])])).

fof(f861,plain,
    ( o_0_0_xboole_0 = sK8(sK0)
    | ~ spl21_116 ),
    inference(resolution,[],[f842,f266])).

fof(f842,plain,
    ( v1_xboole_0(sK8(sK0))
    | ~ spl21_116 ),
    inference(avatar_component_clause,[],[f841])).

fof(f857,plain,
    ( spl21_116
    | spl21_120
    | ~ spl21_88 ),
    inference(avatar_split_clause,[],[f728,f671,f855,f841])).

fof(f671,plain,
    ( spl21_88
  <=> v1_zfmisc_1(sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_88])])).

fof(f728,plain,
    ( v1_zfmisc_1(sK5(sK8(sK0)))
    | v1_xboole_0(sK8(sK0))
    | ~ spl21_88 ),
    inference(resolution,[],[f674,f196])).

fof(f674,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK0)))
        | v1_zfmisc_1(X0) )
    | ~ spl21_88 ),
    inference(resolution,[],[f672,f201])).

fof(f672,plain,
    ( v1_zfmisc_1(sK8(sK0))
    | ~ spl21_88 ),
    inference(avatar_component_clause,[],[f671])).

fof(f849,plain,
    ( spl21_116
    | spl21_118
    | ~ spl21_88 ),
    inference(avatar_split_clause,[],[f725,f671,f847,f841])).

fof(f725,plain,
    ( v1_zfmisc_1(sK2(sK8(sK0)))
    | v1_xboole_0(sK8(sK0))
    | ~ spl21_88 ),
    inference(resolution,[],[f674,f188])).

fof(f835,plain,
    ( spl21_114
    | ~ spl21_94 ),
    inference(avatar_split_clause,[],[f817,f694,f833])).

fof(f817,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK5(sK0))))
    | ~ spl21_94 ),
    inference(resolution,[],[f697,f228])).

fof(f827,plain,
    ( spl21_112
    | ~ spl21_94 ),
    inference(avatar_split_clause,[],[f819,f694,f825])).

fof(f819,plain,
    ( v1_zfmisc_1(sK8(sK5(sK0)))
    | ~ spl21_94 ),
    inference(resolution,[],[f697,f231])).

fof(f810,plain,
    ( spl21_110
    | ~ spl21_92 ),
    inference(avatar_split_clause,[],[f754,f686,f808])).

fof(f754,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK2(sK0))))
    | ~ spl21_92 ),
    inference(resolution,[],[f689,f228])).

fof(f803,plain,
    ( ~ spl21_62
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | ~ spl21_62
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f503])).

fof(f503,plain,
    ( v1_relat_1(sK6(sK12))
    | ~ spl21_62 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl21_62
  <=> v1_relat_1(sK6(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_62])])).

fof(f777,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl21_106 ),
    inference(avatar_component_clause,[],[f776])).

fof(f776,plain,
    ( spl21_106
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_106])])).

fof(f802,plain,
    ( ~ spl21_66
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f787])).

fof(f787,plain,
    ( $false
    | ~ spl21_66
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f536])).

fof(f536,plain,
    ( v1_relat_1(sK6(o_0_0_xboole_0))
    | ~ spl21_66 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl21_66
  <=> v1_relat_1(sK6(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_66])])).

fof(f801,plain,
    ( ~ spl21_24
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f788])).

fof(f788,plain,
    ( $false
    | ~ spl21_24
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f359])).

fof(f359,plain,
    ( v1_relat_1(sK14)
    | ~ spl21_24 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl21_24
  <=> v1_relat_1(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_24])])).

fof(f800,plain,
    ( ~ spl21_28
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | ~ spl21_28
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f373])).

fof(f373,plain,
    ( v1_relat_1(sK15)
    | ~ spl21_28 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl21_28
  <=> v1_relat_1(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_28])])).

fof(f799,plain,
    ( ~ spl21_32
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f790])).

fof(f790,plain,
    ( $false
    | ~ spl21_32
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f387])).

fof(f387,plain,
    ( v1_relat_1(sK16)
    | ~ spl21_32 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl21_32
  <=> v1_relat_1(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_32])])).

fof(f798,plain,
    ( ~ spl21_34
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f791])).

fof(f791,plain,
    ( $false
    | ~ spl21_34
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f394])).

fof(f394,plain,
    ( v1_relat_1(sK17)
    | ~ spl21_34 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl21_34
  <=> v1_relat_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_34])])).

fof(f797,plain,
    ( ~ spl21_38
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f792])).

fof(f792,plain,
    ( $false
    | ~ spl21_38
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f408])).

fof(f408,plain,
    ( v1_relat_1(sK18)
    | ~ spl21_38 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl21_38
  <=> v1_relat_1(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_38])])).

fof(f796,plain,
    ( ~ spl21_42
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f793])).

fof(f793,plain,
    ( $false
    | ~ spl21_42
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f422])).

fof(f795,plain,
    ( ~ spl21_48
    | ~ spl21_106 ),
    inference(avatar_contradiction_clause,[],[f794])).

fof(f794,plain,
    ( $false
    | ~ spl21_48
    | ~ spl21_106 ),
    inference(resolution,[],[f777,f443])).

fof(f443,plain,
    ( v1_relat_1(sK20)
    | ~ spl21_48 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl21_48
  <=> v1_relat_1(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_48])])).

fof(f784,plain,
    ( spl21_106
    | spl21_108 ),
    inference(avatar_split_clause,[],[f758,f782,f776])).

fof(f782,plain,
    ( spl21_108
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_108])])).

fof(f758,plain,(
    ! [X0] :
      ( v1_relat_1(o_0_0_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f202,f485])).

fof(f773,plain,
    ( spl21_104
    | ~ spl21_92 ),
    inference(avatar_split_clause,[],[f756,f686,f771])).

fof(f756,plain,
    ( v1_zfmisc_1(sK8(sK2(sK0)))
    | ~ spl21_92 ),
    inference(resolution,[],[f689,f231])).

fof(f747,plain,
    ( spl21_102
    | ~ spl21_88 ),
    inference(avatar_split_clause,[],[f729,f671,f745])).

fof(f729,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK8(sK0))))
    | ~ spl21_88 ),
    inference(resolution,[],[f674,f228])).

fof(f739,plain,
    ( spl21_100
    | ~ spl21_88 ),
    inference(avatar_split_clause,[],[f731,f671,f737])).

fof(f731,plain,
    ( v1_zfmisc_1(sK8(sK8(sK0)))
    | ~ spl21_88 ),
    inference(resolution,[],[f674,f231])).

fof(f722,plain,
    ( spl21_98
    | ~ spl21_86 ),
    inference(avatar_split_clause,[],[f704,f663,f720])).

fof(f663,plain,
    ( spl21_86
  <=> v1_zfmisc_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_86])])).

fof(f704,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl21_86 ),
    inference(resolution,[],[f666,f228])).

fof(f666,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | v1_zfmisc_1(X0) )
    | ~ spl21_86 ),
    inference(resolution,[],[f664,f201])).

fof(f664,plain,
    ( v1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl21_86 ),
    inference(avatar_component_clause,[],[f663])).

fof(f714,plain,
    ( spl21_96
    | ~ spl21_86 ),
    inference(avatar_split_clause,[],[f706,f663,f712])).

fof(f706,plain,
    ( v1_zfmisc_1(sK8(o_0_0_xboole_0))
    | ~ spl21_86 ),
    inference(resolution,[],[f666,f231])).

fof(f696,plain,
    ( spl21_94
    | spl21_1
    | ~ spl21_2 ),
    inference(avatar_split_clause,[],[f657,f281,f274,f694])).

fof(f657,plain,
    ( v1_zfmisc_1(sK5(sK0))
    | ~ spl21_1
    | ~ spl21_2 ),
    inference(subsumption_resolution,[],[f652,f275])).

fof(f652,plain,
    ( v1_zfmisc_1(sK5(sK0))
    | v1_xboole_0(sK0)
    | ~ spl21_2 ),
    inference(resolution,[],[f637,f196])).

fof(f637,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
        | v1_zfmisc_1(X4) )
    | ~ spl21_2 ),
    inference(resolution,[],[f201,f282])).

fof(f688,plain,
    ( spl21_92
    | spl21_1
    | ~ spl21_2 ),
    inference(avatar_split_clause,[],[f656,f281,f274,f686])).

fof(f656,plain,
    ( v1_zfmisc_1(sK2(sK0))
    | ~ spl21_1
    | ~ spl21_2 ),
    inference(subsumption_resolution,[],[f649,f275])).

fof(f649,plain,
    ( v1_zfmisc_1(sK2(sK0))
    | v1_xboole_0(sK0)
    | ~ spl21_2 ),
    inference(resolution,[],[f637,f188])).

fof(f681,plain,
    ( spl21_90
    | ~ spl21_2 ),
    inference(avatar_split_clause,[],[f653,f281,f679])).

fof(f653,plain,
    ( v1_zfmisc_1(sK6(k1_zfmisc_1(sK0)))
    | ~ spl21_2 ),
    inference(resolution,[],[f637,f228])).

fof(f673,plain,
    ( spl21_88
    | ~ spl21_2 ),
    inference(avatar_split_clause,[],[f655,f281,f671])).

fof(f655,plain,
    ( v1_zfmisc_1(sK8(sK0))
    | ~ spl21_2 ),
    inference(resolution,[],[f637,f231])).

fof(f665,plain,
    ( spl21_86
    | ~ spl21_2 ),
    inference(avatar_split_clause,[],[f648,f281,f663])).

fof(f648,plain,
    ( v1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl21_2 ),
    inference(resolution,[],[f637,f485])).

fof(f647,plain,
    ( spl21_84
    | ~ spl21_72 ),
    inference(avatar_split_clause,[],[f634,f578,f645])).

fof(f645,plain,
    ( spl21_84
  <=> v1_funct_1(sK6(sK8(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_84])])).

fof(f634,plain,
    ( v1_funct_1(sK6(sK8(sK12)))
    | ~ spl21_72 ),
    inference(resolution,[],[f582,f228])).

fof(f582,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK8(sK12))
        | v1_funct_1(X1) )
    | ~ spl21_72 ),
    inference(resolution,[],[f579,f199])).

fof(f627,plain,
    ( spl21_82
    | spl21_15
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f562,f330,f323,f625])).

fof(f323,plain,
    ( spl21_15
  <=> ~ v1_xboole_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_15])])).

fof(f330,plain,
    ( spl21_16
  <=> v4_funct_1(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_16])])).

fof(f562,plain,
    ( v4_funct_1(sK5(sK12))
    | ~ spl21_15
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f555,f324])).

fof(f324,plain,
    ( ~ v1_xboole_0(sK12)
    | ~ spl21_15 ),
    inference(avatar_component_clause,[],[f323])).

fof(f555,plain,
    ( v4_funct_1(sK5(sK12))
    | v1_xboole_0(sK12)
    | ~ spl21_16 ),
    inference(resolution,[],[f522,f196])).

fof(f522,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12))
        | v4_funct_1(X0) )
    | ~ spl21_16 ),
    inference(resolution,[],[f200,f331])).

fof(f331,plain,
    ( v4_funct_1(sK12)
    | ~ spl21_16 ),
    inference(avatar_component_clause,[],[f330])).

fof(f617,plain,
    ( spl21_80
    | spl21_15
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f561,f330,f323,f615])).

fof(f561,plain,
    ( v4_funct_1(sK4(sK12))
    | ~ spl21_15
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f554,f324])).

fof(f554,plain,
    ( v4_funct_1(sK4(sK12))
    | v1_xboole_0(sK12)
    | ~ spl21_16 ),
    inference(resolution,[],[f522,f193])).

fof(f193,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f87,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc1_tex_2)).

fof(f607,plain,
    ( spl21_78
    | spl21_15
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f560,f330,f323,f605])).

fof(f560,plain,
    ( v4_funct_1(sK3(sK12))
    | ~ spl21_15
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f553,f324])).

fof(f553,plain,
    ( v4_funct_1(sK3(sK12))
    | v1_xboole_0(sK12)
    | ~ spl21_16 ),
    inference(resolution,[],[f522,f190])).

fof(f190,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK3(X0))
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f86,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK3(X0))
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc3_realset1)).

fof(f597,plain,
    ( spl21_76
    | spl21_15
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f559,f330,f323,f595])).

fof(f559,plain,
    ( v4_funct_1(sK2(sK12))
    | ~ spl21_15
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f552,f324])).

fof(f552,plain,
    ( v4_funct_1(sK2(sK12))
    | v1_xboole_0(sK12)
    | ~ spl21_16 ),
    inference(resolution,[],[f522,f188])).

fof(f590,plain,
    ( spl21_74
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f556,f330,f588])).

fof(f588,plain,
    ( spl21_74
  <=> v4_funct_1(sK6(k1_zfmisc_1(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_74])])).

fof(f556,plain,
    ( v4_funct_1(sK6(k1_zfmisc_1(sK12)))
    | ~ spl21_16 ),
    inference(resolution,[],[f522,f228])).

fof(f580,plain,
    ( spl21_72
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f558,f330,f578])).

fof(f558,plain,
    ( v4_funct_1(sK8(sK12))
    | ~ spl21_16 ),
    inference(resolution,[],[f522,f231])).

fof(f570,plain,
    ( spl21_70
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f551,f330,f568])).

fof(f551,plain,
    ( v4_funct_1(o_0_0_xboole_0)
    | ~ spl21_16 ),
    inference(resolution,[],[f522,f485])).

fof(f550,plain,(
    spl21_68 ),
    inference(avatar_split_clause,[],[f543,f548])).

fof(f548,plain,
    ( spl21_68
  <=> v1_funct_1(sK6(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_68])])).

fof(f543,plain,(
    v1_funct_1(sK6(o_0_0_xboole_0)) ),
    inference(resolution,[],[f541,f228])).

fof(f541,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,o_0_0_xboole_0)
      | v1_funct_1(X0) ) ),
    inference(forward_demodulation,[],[f538,f482])).

fof(f538,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X0)
      | ~ m1_subset_1(X0,sK7(X1)) ) ),
    inference(resolution,[],[f506,f230])).

fof(f506,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | v1_funct_1(X1)
      | ~ m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f199,f203])).

fof(f203,plain,(
    ! [X0] :
      ( v4_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( v4_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v4_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc8_funct_1)).

fof(f537,plain,(
    spl21_66 ),
    inference(avatar_split_clause,[],[f530,f535])).

fof(f530,plain,(
    v1_relat_1(sK6(o_0_0_xboole_0)) ),
    inference(resolution,[],[f528,f228])).

fof(f528,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,o_0_0_xboole_0)
      | v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f525,f482])).

fof(f525,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
      | ~ m1_subset_1(X0,sK7(X1)) ) ),
    inference(resolution,[],[f496,f230])).

fof(f496,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | v1_relat_1(X1)
      | ~ m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f198,f203])).

fof(f514,plain,
    ( spl21_64
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f507,f330,f512])).

fof(f512,plain,
    ( spl21_64
  <=> v1_funct_1(sK6(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_64])])).

fof(f507,plain,
    ( v1_funct_1(sK6(sK12))
    | ~ spl21_16 ),
    inference(resolution,[],[f505,f228])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK12)
        | v1_funct_1(X0) )
    | ~ spl21_16 ),
    inference(resolution,[],[f199,f331])).

fof(f504,plain,
    ( spl21_62
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f497,f330,f502])).

fof(f497,plain,
    ( v1_relat_1(sK6(sK12))
    | ~ spl21_16 ),
    inference(resolution,[],[f495,f228])).

fof(f495,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK12)
        | v1_relat_1(X0) )
    | ~ spl21_16 ),
    inference(resolution,[],[f198,f331])).

fof(f493,plain,
    ( spl21_60
    | ~ spl21_8 ),
    inference(avatar_split_clause,[],[f484,f302,f491])).

fof(f491,plain,
    ( spl21_60
  <=> o_0_0_xboole_0 = sK10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_60])])).

fof(f302,plain,
    ( spl21_8
  <=> v1_xboole_0(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_8])])).

fof(f484,plain,
    ( o_0_0_xboole_0 = sK10
    | ~ spl21_8 ),
    inference(resolution,[],[f266,f303])).

fof(f303,plain,
    ( v1_xboole_0(sK10)
    | ~ spl21_8 ),
    inference(avatar_component_clause,[],[f302])).

fof(f481,plain,
    ( ~ spl21_59
    | spl21_47 ),
    inference(avatar_split_clause,[],[f474,f435,f479])).

fof(f479,plain,
    ( spl21_59
  <=> ~ v1_xboole_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_59])])).

fof(f474,plain,
    ( ~ v1_xboole_0(sK19)
    | ~ spl21_47 ),
    inference(resolution,[],[f269,f436])).

fof(f269,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f268,f207])).

fof(f207,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc1_relat_1)).

fof(f268,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f225,f206])).

fof(f206,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc1_funct_1)).

fof(f225,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',cc4_funct_1)).

fof(f472,plain,(
    spl21_56 ),
    inference(avatar_split_clause,[],[f177,f470])).

fof(f177,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f136])).

fof(f136,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f79,f135,f134])).

fof(f134,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f135,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK1),X0)
        & m1_subset_1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',t6_tex_2)).

fof(f465,plain,(
    spl21_54 ),
    inference(avatar_split_clause,[],[f181,f463])).

fof(f463,plain,
    ( spl21_54
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_54])])).

fof(f458,plain,(
    spl21_52 ),
    inference(avatar_split_clause,[],[f176,f456])).

fof(f176,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f136])).

fof(f451,plain,(
    spl21_50 ),
    inference(avatar_split_clause,[],[f264,f449])).

fof(f449,plain,
    ( spl21_50
  <=> v1_funct_1(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_50])])).

fof(f264,plain,(
    v1_funct_1(sK20) ),
    inference(cnf_transformation,[],[f174])).

fof(f174,plain,
    ( v1_funct_1(sK20)
    & v1_relat_1(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f77,f173])).

fof(f173,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK20)
      & v1_relat_1(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc2_funct_1)).

fof(f444,plain,(
    spl21_48 ),
    inference(avatar_split_clause,[],[f263,f442])).

fof(f263,plain,(
    v1_relat_1(sK20) ),
    inference(cnf_transformation,[],[f174])).

fof(f437,plain,(
    ~ spl21_47 ),
    inference(avatar_split_clause,[],[f262,f435])).

fof(f262,plain,(
    ~ v3_funct_1(sK19) ),
    inference(cnf_transformation,[],[f172])).

fof(f172,plain,
    ( ~ v3_funct_1(sK19)
    & v1_funct_1(sK19)
    & v1_relat_1(sK19) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f9,f171])).

fof(f171,plain,
    ( ? [X0] :
        ( ~ v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v3_funct_1(sK19)
      & v1_funct_1(sK19)
      & v1_relat_1(sK19) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ? [X0] :
      ( ~ v3_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc5_funct_1)).

fof(f430,plain,(
    spl21_44 ),
    inference(avatar_split_clause,[],[f261,f428])).

fof(f261,plain,(
    v1_funct_1(sK19) ),
    inference(cnf_transformation,[],[f172])).

fof(f423,plain,(
    spl21_42 ),
    inference(avatar_split_clause,[],[f260,f421])).

fof(f260,plain,(
    v1_relat_1(sK19) ),
    inference(cnf_transformation,[],[f172])).

fof(f416,plain,(
    spl21_40 ),
    inference(avatar_split_clause,[],[f259,f414])).

fof(f414,plain,
    ( spl21_40
  <=> v1_funct_1(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_40])])).

fof(f259,plain,(
    v1_funct_1(sK18) ),
    inference(cnf_transformation,[],[f170])).

fof(f170,plain,
    ( v1_funct_1(sK18)
    & v1_relat_1(sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f36,f169])).

fof(f169,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK18)
      & v1_relat_1(sK18) ) ),
    introduced(choice_axiom,[])).

fof(f36,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc1_funct_1)).

fof(f409,plain,(
    spl21_38 ),
    inference(avatar_split_clause,[],[f258,f407])).

fof(f258,plain,(
    v1_relat_1(sK18) ),
    inference(cnf_transformation,[],[f170])).

fof(f402,plain,(
    spl21_36 ),
    inference(avatar_split_clause,[],[f257,f400])).

fof(f400,plain,
    ( spl21_36
  <=> v1_funct_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_36])])).

fof(f257,plain,(
    v1_funct_1(sK17) ),
    inference(cnf_transformation,[],[f168])).

fof(f168,plain,
    ( v1_funct_1(sK17)
    & v1_relat_1(sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f75,f167])).

fof(f167,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK17)
      & v1_relat_1(sK17) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc3_funct_1)).

fof(f395,plain,(
    spl21_34 ),
    inference(avatar_split_clause,[],[f256,f393])).

fof(f256,plain,(
    v1_relat_1(sK17) ),
    inference(cnf_transformation,[],[f168])).

fof(f388,plain,(
    spl21_32 ),
    inference(avatar_split_clause,[],[f255,f386])).

fof(f255,plain,(
    v1_relat_1(sK16) ),
    inference(cnf_transformation,[],[f166])).

fof(f166,plain,(
    v1_relat_1(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f73,f165])).

fof(f165,plain,
    ( ? [X0] : v1_relat_1(X0)
   => v1_relat_1(sK16) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ? [X0] : v1_relat_1(X0) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ? [X0] :
      ( v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc2_relat_1)).

fof(f381,plain,(
    spl21_30 ),
    inference(avatar_split_clause,[],[f254,f379])).

fof(f379,plain,
    ( spl21_30
  <=> v1_funct_1(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_30])])).

fof(f254,plain,(
    v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f164])).

fof(f164,plain,
    ( v1_funct_1(sK15)
    & v1_relat_1(sK15)
    & ~ v1_xboole_0(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f74,f163])).

fof(f163,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_funct_1(sK15)
      & v1_relat_1(sK15)
      & ~ v1_xboole_0(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc4_funct_1)).

fof(f374,plain,(
    spl21_28 ),
    inference(avatar_split_clause,[],[f253,f372])).

fof(f253,plain,(
    v1_relat_1(sK15) ),
    inference(cnf_transformation,[],[f164])).

fof(f367,plain,(
    ~ spl21_27 ),
    inference(avatar_split_clause,[],[f252,f365])).

fof(f365,plain,
    ( spl21_27
  <=> ~ v1_xboole_0(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_27])])).

fof(f252,plain,(
    ~ v1_xboole_0(sK15) ),
    inference(cnf_transformation,[],[f164])).

fof(f360,plain,(
    spl21_24 ),
    inference(avatar_split_clause,[],[f251,f358])).

fof(f251,plain,(
    v1_relat_1(sK14) ),
    inference(cnf_transformation,[],[f162])).

fof(f162,plain,
    ( v1_relat_1(sK14)
    & ~ v1_xboole_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f37,f161])).

fof(f161,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK14)
      & ~ v1_xboole_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f37,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc1_relat_1)).

fof(f353,plain,(
    ~ spl21_23 ),
    inference(avatar_split_clause,[],[f250,f351])).

fof(f351,plain,
    ( spl21_23
  <=> ~ v1_xboole_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_23])])).

fof(f250,plain,(
    ~ v1_xboole_0(sK14) ),
    inference(cnf_transformation,[],[f162])).

fof(f346,plain,(
    spl21_20 ),
    inference(avatar_split_clause,[],[f249,f344])).

fof(f249,plain,(
    v1_zfmisc_1(sK13) ),
    inference(cnf_transformation,[],[f160])).

fof(f160,plain,
    ( v1_zfmisc_1(sK13)
    & ~ v1_xboole_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f62,f159])).

fof(f159,plain,
    ( ? [X0] :
        ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_zfmisc_1(sK13)
      & ~ v1_xboole_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f62,axiom,(
    ? [X0] :
      ( v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc1_realset1)).

fof(f339,plain,(
    ~ spl21_19 ),
    inference(avatar_split_clause,[],[f248,f337])).

fof(f248,plain,(
    ~ v1_xboole_0(sK13) ),
    inference(cnf_transformation,[],[f160])).

fof(f332,plain,(
    spl21_16 ),
    inference(avatar_split_clause,[],[f247,f330])).

fof(f247,plain,(
    v4_funct_1(sK12) ),
    inference(cnf_transformation,[],[f158])).

fof(f158,plain,
    ( v4_funct_1(sK12)
    & ~ v1_xboole_0(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f44,f157])).

fof(f157,plain,
    ( ? [X0] :
        ( v4_funct_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v4_funct_1(sK12)
      & ~ v1_xboole_0(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f44,axiom,(
    ? [X0] :
      ( v4_funct_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc7_funct_1)).

fof(f325,plain,(
    ~ spl21_15 ),
    inference(avatar_split_clause,[],[f246,f323])).

fof(f246,plain,(
    ~ v1_xboole_0(sK12) ),
    inference(cnf_transformation,[],[f158])).

fof(f318,plain,(
    ~ spl21_13 ),
    inference(avatar_split_clause,[],[f245,f316])).

fof(f316,plain,
    ( spl21_13
  <=> ~ v1_zfmisc_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_13])])).

fof(f245,plain,(
    ~ v1_zfmisc_1(sK11) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,
    ( ~ v1_zfmisc_1(sK11)
    & ~ v1_xboole_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f64,f155])).

fof(f155,plain,
    ( ? [X0] :
        ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ~ v1_zfmisc_1(sK11)
      & ~ v1_xboole_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f64,axiom,(
    ? [X0] :
      ( ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc2_realset1)).

fof(f311,plain,(
    ~ spl21_11 ),
    inference(avatar_split_clause,[],[f244,f309])).

fof(f309,plain,
    ( spl21_11
  <=> ~ v1_xboole_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_11])])).

fof(f244,plain,(
    ~ v1_xboole_0(sK11) ),
    inference(cnf_transformation,[],[f156])).

fof(f304,plain,(
    spl21_8 ),
    inference(avatar_split_clause,[],[f243,f302])).

fof(f243,plain,(
    v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f154])).

fof(f154,plain,(
    v1_xboole_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f63,f153])).

fof(f153,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK10) ),
    introduced(choice_axiom,[])).

fof(f63,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc1_xboole_0)).

fof(f297,plain,(
    ~ spl21_7 ),
    inference(avatar_split_clause,[],[f242,f295])).

fof(f295,plain,
    ( spl21_7
  <=> ~ v1_xboole_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_7])])).

fof(f242,plain,(
    ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f152])).

fof(f152,plain,(
    ~ v1_xboole_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f65,f151])).

fof(f151,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK9) ),
    introduced(choice_axiom,[])).

fof(f65,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',rc2_xboole_0)).

fof(f290,plain,(
    spl21_4 ),
    inference(avatar_split_clause,[],[f179,f288])).

fof(f179,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t6_tex_2.p',dt_o_0_0_xboole_0)).

fof(f283,plain,(
    spl21_2 ),
    inference(avatar_split_clause,[],[f178,f281])).

fof(f178,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f136])).

fof(f276,plain,(
    ~ spl21_1 ),
    inference(avatar_split_clause,[],[f175,f274])).

fof(f175,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f136])).
%------------------------------------------------------------------------------
