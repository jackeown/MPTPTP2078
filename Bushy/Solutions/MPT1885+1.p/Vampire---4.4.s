%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t53_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:53 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  874 (3038 expanded)
%              Number of leaves         :  213 (1279 expanded)
%              Depth                    :   14
%              Number of atoms          : 3173 (9953 expanded)
%              Number of equality atoms :  130 ( 890 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :   14 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f342,f349,f356,f363,f370,f377,f384,f391,f398,f405,f412,f419,f426,f433,f440,f447,f454,f461,f468,f475,f482,f489,f496,f503,f510,f517,f524,f531,f538,f545,f552,f559,f566,f573,f580,f587,f614,f633,f658,f673,f731,f746,f772,f791,f794,f802,f822,f842,f861,f872,f883,f901,f904,f912,f928,f942,f973,f992,f1003,f1014,f1028,f1049,f1054,f1059,f1084,f1088,f1092,f1096,f1105,f1114,f1123,f1135,f1136,f1154,f1161,f1168,f1175,f1182,f1189,f1191,f1192,f1210,f1214,f1226,f1227,f1228,f1229,f1230,f1231,f1243,f1250,f1260,f1268,f1295,f1329,f1332,f1340,f1356,f1370,f1384,f1399,f1435,f1465,f1476,f1487,f1498,f1525,f1530,f1535,f1540,f1545,f1551,f1567,f1577,f1587,f1597,f1618,f1629,f1637,f1667,f1688,f1714,f1740,f1743,f1771,f1782,f1800,f1803,f1806,f1807,f1808,f1809,f1827,f1834,f1841,f1848,f1855,f1862,f1881,f1888,f1896,f1903,f1910,f1917,f1924,f1931,f1933,f1965,f1984,f2018,f2022,f2026,f2030,f2034,f2039,f2054,f2068,f2076,f2084,f2092,f2100,f2108,f2134,f2143,f2176,f2184,f2192,f2226])).

fof(f2226,plain,
    ( ~ spl22_0
    | spl22_5
    | ~ spl22_6
    | ~ spl22_8
    | ~ spl22_86
    | ~ spl22_94
    | spl22_97 ),
    inference(avatar_contradiction_clause,[],[f2225])).

fof(f2225,plain,
    ( $false
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_6
    | ~ spl22_8
    | ~ spl22_86
    | ~ spl22_94
    | ~ spl22_97 ),
    inference(subsumption_resolution,[],[f2224,f841])).

fof(f841,plain,
    ( ~ v4_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl22_97 ),
    inference(avatar_component_clause,[],[f840])).

fof(f840,plain,
    ( spl22_97
  <=> ~ v4_tex_2(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_97])])).

fof(f2224,plain,
    ( v4_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_6
    | ~ spl22_8
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f2223,f355])).

fof(f355,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl22_5 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl22_5
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5])])).

fof(f2223,plain,
    ( v2_struct_0(sK0)
    | v4_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_6
    | ~ spl22_8
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f2222,f362])).

fof(f362,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl22_6 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl22_6
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_6])])).

fof(f2222,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f2221,f341])).

fof(f341,plain,
    ( l1_pre_topc(sK0)
    | ~ spl22_0 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl22_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_0])])).

fof(f2221,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl22_8
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f2220,f369])).

fof(f369,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_8 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl22_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_8])])).

fof(f2220,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(resolution,[],[f1200,f771])).

fof(f771,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_86 ),
    inference(avatar_component_clause,[],[f770])).

fof(f770,plain,
    ( spl22_86
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_86])])).

fof(f1200,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v3_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | v4_tex_2(sK2(sK0,sK1),X0) )
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f1194,f821])).

fof(f821,plain,
    ( u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_94 ),
    inference(avatar_component_clause,[],[f820])).

fof(f820,plain,
    ( spl22_94
  <=> u1_struct_0(sK2(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_94])])).

fof(f1194,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | v4_tex_2(sK2(sK0,sK1),X0)
        | ~ v3_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) )
    | ~ spl22_94 ),
    inference(superposition,[],[f334,f821])).

fof(f334,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f292])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f242])).

fof(f242,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f241])).

fof(f241,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f218])).

fof(f218,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',t51_tex_2)).

fof(f2192,plain,
    ( ~ spl22_353
    | spl22_271
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f2185,f1825,f1798,f2190])).

fof(f2190,plain,
    ( spl22_353
  <=> ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_353])])).

fof(f1798,plain,
    ( spl22_271
  <=> ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_271])])).

fof(f1825,plain,
    ( spl22_272
  <=> sK10(k1_zfmisc_1(sK12(sK1))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_272])])).

fof(f2185,plain,
    ( ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13))
    | ~ spl22_271
    | ~ spl22_272 ),
    inference(forward_demodulation,[],[f1799,f1826])).

fof(f1826,plain,
    ( sK10(k1_zfmisc_1(sK12(sK1))) = sK13
    | ~ spl22_272 ),
    inference(avatar_component_clause,[],[f1825])).

fof(f1799,plain,
    ( ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_271 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f2184,plain,
    ( ~ spl22_351
    | spl22_269
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f2177,f1825,f1789,f2182])).

fof(f2182,plain,
    ( spl22_351
  <=> ~ v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_351])])).

fof(f1789,plain,
    ( spl22_269
  <=> ~ v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_269])])).

fof(f2177,plain,
    ( ~ v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13))
    | ~ spl22_269
    | ~ spl22_272 ),
    inference(forward_demodulation,[],[f1790,f1826])).

fof(f1790,plain,
    ( ~ v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_269 ),
    inference(avatar_component_clause,[],[f1789])).

fof(f2176,plain,
    ( spl22_348
    | spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | spl22_197 ),
    inference(avatar_split_clause,[],[f2169,f1460,f1362,f1338,f990,f2174])).

fof(f2174,plain,
    ( spl22_348
  <=> u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1)))))) = sK10(k1_zfmisc_1(sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_348])])).

fof(f990,plain,
    ( spl22_125
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_125])])).

fof(f1338,plain,
    ( spl22_176
  <=> l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_176])])).

fof(f1362,plain,
    ( spl22_182
  <=> u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) = sK12(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_182])])).

fof(f1460,plain,
    ( spl22_197
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_197])])).

fof(f2169,plain,
    ( u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1)))))) = sK10(k1_zfmisc_1(sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_197 ),
    inference(forward_demodulation,[],[f2168,f1363])).

fof(f1363,plain,
    ( u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) = sK12(sK12(sK1))
    | ~ spl22_182 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f2168,plain,
    ( u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))) = sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_197 ),
    inference(subsumption_resolution,[],[f2167,f991])).

fof(f991,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125 ),
    inference(avatar_component_clause,[],[f990])).

fof(f2167,plain,
    ( v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))) = sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))))
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_197 ),
    inference(subsumption_resolution,[],[f2166,f1339])).

fof(f1339,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_176 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f2166,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))) = sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))))
    | ~ spl22_182
    | ~ spl22_197 ),
    inference(subsumption_resolution,[],[f2159,f1461])).

fof(f1461,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK12(sK1)))))
    | ~ spl22_197 ),
    inference(avatar_component_clause,[],[f1460])).

fof(f2159,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))) = sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))))
    | ~ spl22_182 ),
    inference(superposition,[],[f810,f1363])).

fof(f810,plain,(
    ! [X0] :
      ( v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(sK2(X0,sK10(k1_zfmisc_1(u1_struct_0(X0))))) = sK10(k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f268,f293])).

fof(f293,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',existence_m1_subset_1)).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f227])).

fof(f227,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f213])).

fof(f213,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',t10_tsep_1)).

fof(f2143,plain,
    ( ~ spl22_347
    | spl22_229
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f2136,f1825,f1613,f2141])).

fof(f2141,plain,
    ( spl22_347
  <=> ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_347])])).

fof(f1613,plain,
    ( spl22_229
  <=> ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_229])])).

fof(f2136,plain,
    ( ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13))
    | ~ spl22_229
    | ~ spl22_272 ),
    inference(forward_demodulation,[],[f1614,f1826])).

fof(f1614,plain,
    ( ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_229 ),
    inference(avatar_component_clause,[],[f1613])).

fof(f2134,plain,
    ( spl22_338
    | ~ spl22_341
    | ~ spl22_343
    | ~ spl22_345
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f2109,f1963,f820,f800,f729,f2132,f2126,f2120,f2114])).

fof(f2114,plain,
    ( spl22_338
  <=> v4_tex_2(sK2(sK0,sK12(u1_struct_0(sK0))),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_338])])).

fof(f2120,plain,
    ( spl22_341
  <=> ~ m1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_341])])).

fof(f2126,plain,
    ( spl22_343
  <=> ~ v3_tex_2(sK12(u1_struct_0(sK0)),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_343])])).

fof(f2132,plain,
    ( spl22_345
  <=> ~ m1_subset_1(sK12(u1_struct_0(sK0)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_345])])).

fof(f729,plain,
    ( spl22_83
  <=> ~ v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_83])])).

fof(f800,plain,
    ( spl22_92
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_92])])).

fof(f1963,plain,
    ( spl22_300
  <=> u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))) = sK12(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_300])])).

fof(f2109,plain,
    ( ~ m1_subset_1(sK12(u1_struct_0(sK0)),k1_zfmisc_1(sK1))
    | ~ v3_tex_2(sK12(u1_struct_0(sK0)),sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK0,sK12(u1_struct_0(sK0))),sK2(sK0,sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_300 ),
    inference(forward_demodulation,[],[f2001,f1964])).

fof(f1964,plain,
    ( u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))) = sK12(u1_struct_0(sK0))
    | ~ spl22_300 ),
    inference(avatar_component_clause,[],[f1963])).

fof(f2001,plain,
    ( ~ v3_tex_2(sK12(u1_struct_0(sK0)),sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK0,sK12(u1_struct_0(sK0))),sK2(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_300 ),
    inference(superposition,[],[f1204,f1964])).

fof(f1204,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(u1_struct_0(X0),sK2(sK0,sK1))
        | ~ m1_pre_topc(X0,sK2(sK0,sK1))
        | v4_tex_2(X0,sK2(sK0,sK1))
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(sK1)) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1203,f730])).

fof(f730,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_83 ),
    inference(avatar_component_clause,[],[f729])).

fof(f1203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(sK1))
        | ~ m1_pre_topc(X0,sK2(sK0,sK1))
        | v2_struct_0(sK2(sK0,sK1))
        | v4_tex_2(X0,sK2(sK0,sK1))
        | ~ v3_tex_2(u1_struct_0(X0),sK2(sK0,sK1)) )
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1197,f801])).

fof(f801,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_92 ),
    inference(avatar_component_clause,[],[f800])).

fof(f1197,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | ~ m1_pre_topc(X0,sK2(sK0,sK1))
        | v2_struct_0(sK2(sK0,sK1))
        | v4_tex_2(X0,sK2(sK0,sK1))
        | ~ v3_tex_2(u1_struct_0(X0),sK2(sK0,sK1)) )
    | ~ spl22_94 ),
    inference(superposition,[],[f334,f821])).

fof(f2108,plain,
    ( ~ spl22_307
    | spl22_304
    | spl22_326
    | spl22_336
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f2101,f1963,f2106,f2066,f2007,f2013])).

fof(f2013,plain,
    ( spl22_307
  <=> ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_307])])).

fof(f2007,plain,
    ( spl22_304
  <=> v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_304])])).

fof(f2066,plain,
    ( spl22_326
  <=> v1_xboole_0(sK12(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_326])])).

fof(f2106,plain,
    ( spl22_336
  <=> u1_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0))))) = sK12(sK12(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_336])])).

fof(f2101,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0))))) = sK12(sK12(u1_struct_0(sK0)))
    | v1_xboole_0(sK12(u1_struct_0(sK0)))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(forward_demodulation,[],[f2000,f1964])).

fof(f2000,plain,
    ( v1_xboole_0(sK12(u1_struct_0(sK0)))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | u1_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))))) = sK12(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(superposition,[],[f823,f1964])).

fof(f823,plain,(
    ! [X1] :
      ( v1_xboole_0(u1_struct_0(X1))
      | v2_struct_0(X1)
      | u1_struct_0(sK2(X1,sK12(u1_struct_0(X1)))) = sK12(u1_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f811,f298])).

fof(f298,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK12(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f244])).

fof(f244,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f152])).

fof(f152,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc1_subset_1)).

fof(f811,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v1_xboole_0(sK12(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | u1_struct_0(sK2(X1,sK12(u1_struct_0(X1)))) = sK12(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f268,f297])).

fof(f297,plain,(
    ! [X0] :
      ( m1_subset_1(sK12(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f244])).

fof(f2100,plain,
    ( ~ spl22_307
    | spl22_304
    | spl22_334
    | spl22_326
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f2093,f1963,f2066,f2098,f2007,f2013])).

fof(f2098,plain,
    ( spl22_334
  <=> m1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0)))),sK2(sK0,sK12(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_334])])).

fof(f2093,plain,
    ( v1_xboole_0(sK12(u1_struct_0(sK0)))
    | m1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0)))),sK2(sK0,sK12(u1_struct_0(sK0))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(forward_demodulation,[],[f1999,f1964])).

fof(f1999,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0)))),sK2(sK0,sK12(u1_struct_0(sK0))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))))
    | ~ spl22_300 ),
    inference(superposition,[],[f773,f1964])).

fof(f773,plain,(
    ! [X1] :
      ( m1_pre_topc(sK2(X1,sK12(u1_struct_0(X1))),X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f761,f298])).

fof(f761,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v1_xboole_0(sK12(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | m1_pre_topc(sK2(X1,sK12(u1_struct_0(X1))),X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f267,f297])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f227])).

fof(f2092,plain,
    ( ~ spl22_307
    | spl22_304
    | spl22_332
    | spl22_322
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f2085,f1963,f2052,f2090,f2007,f2013])).

fof(f2090,plain,
    ( spl22_332
  <=> m1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0))))),sK2(sK0,sK12(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_332])])).

fof(f2052,plain,
    ( spl22_322
  <=> v1_xboole_0(sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_322])])).

fof(f2085,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0)))))
    | m1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0))))),sK2(sK0,sK12(u1_struct_0(sK0))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(forward_demodulation,[],[f1998,f1964])).

fof(f1998,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0))))),sK2(sK0,sK12(u1_struct_0(sK0))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(superposition,[],[f760,f1964])).

fof(f760,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2(X0,sK10(k1_zfmisc_1(u1_struct_0(X0)))),X0)
      | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f267,f293])).

fof(f2084,plain,
    ( ~ spl22_307
    | spl22_304
    | spl22_330
    | spl22_326
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f2077,f1963,f2066,f2082,f2007,f2013])).

fof(f2082,plain,
    ( spl22_330
  <=> v1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_330])])).

fof(f2077,plain,
    ( v1_xboole_0(sK12(u1_struct_0(sK0)))
    | v1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0)))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(forward_demodulation,[],[f1997,f1964])).

fof(f1997,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0)))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))))
    | ~ spl22_300 ),
    inference(superposition,[],[f747,f1964])).

fof(f747,plain,(
    ! [X1] :
      ( v1_pre_topc(sK2(X1,sK12(u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f735,f298])).

fof(f735,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v1_xboole_0(sK12(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | v1_pre_topc(sK2(X1,sK12(u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f266,f297])).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_pre_topc(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f227])).

fof(f2076,plain,
    ( ~ spl22_307
    | spl22_304
    | spl22_328
    | spl22_322
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f2069,f1963,f2052,f2074,f2007,f2013])).

fof(f2074,plain,
    ( spl22_328
  <=> v1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_328])])).

fof(f2069,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0)))))
    | v1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0))))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(forward_demodulation,[],[f1996,f1964])).

fof(f1996,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(superposition,[],[f734,f1964])).

fof(f734,plain,(
    ! [X0] :
      ( v1_pre_topc(sK2(X0,sK10(k1_zfmisc_1(u1_struct_0(X0)))))
      | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f266,f293])).

fof(f2068,plain,
    ( ~ spl22_307
    | spl22_304
    | ~ spl22_325
    | spl22_326
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f2055,f1963,f2066,f2060,f2007,f2013])).

fof(f2060,plain,
    ( spl22_325
  <=> ~ v2_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_325])])).

fof(f2055,plain,
    ( v1_xboole_0(sK12(u1_struct_0(sK0)))
    | ~ v2_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0)))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(forward_demodulation,[],[f1995,f1964])).

fof(f1995,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK12(sK12(u1_struct_0(sK0)))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))))
    | ~ spl22_300 ),
    inference(superposition,[],[f732,f1964])).

fof(f732,plain,(
    ! [X1] :
      ( ~ v2_struct_0(sK2(X1,sK12(u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f720,f298])).

fof(f720,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v1_xboole_0(sK12(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ v2_struct_0(sK2(X1,sK12(u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f265,f297])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f227])).

fof(f2054,plain,
    ( ~ spl22_307
    | spl22_304
    | ~ spl22_321
    | spl22_322
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f2041,f1963,f2052,f2046,f2007,f2013])).

fof(f2046,plain,
    ( spl22_321
  <=> ~ v2_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_321])])).

fof(f2041,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0)))))
    | ~ v2_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0))))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(forward_demodulation,[],[f1994,f1964])).

fof(f1994,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),sK10(k1_zfmisc_1(sK12(u1_struct_0(sK0))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))))))
    | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
    | ~ spl22_300 ),
    inference(superposition,[],[f719,f1964])).

fof(f719,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0,sK10(k1_zfmisc_1(u1_struct_0(X0)))))
      | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f265,f293])).

fof(f2039,plain,
    ( spl22_304
    | ~ spl22_307
    | spl22_318
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f1992,f1963,f2037,f2013,f2007])).

fof(f2037,plain,
    ( spl22_318
  <=> ! [X6] :
        ( ~ m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | v3_tex_2(u1_struct_0(X6),sK2(sK0,sK12(u1_struct_0(sK0))))
        | ~ v4_tex_2(X6,sK2(sK0,sK12(u1_struct_0(sK0))))
        | ~ m1_pre_topc(X6,sK2(sK0,sK12(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_318])])).

fof(f1992,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
        | ~ m1_pre_topc(X6,sK2(sK0,sK12(u1_struct_0(sK0))))
        | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
        | ~ v4_tex_2(X6,sK2(sK0,sK12(u1_struct_0(sK0))))
        | v3_tex_2(u1_struct_0(X6),sK2(sK0,sK12(u1_struct_0(sK0)))) )
    | ~ spl22_300 ),
    inference(superposition,[],[f335,f1964])).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v4_tex_2(X1,X0)
      | v3_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f291])).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v4_tex_2(X1,X0)
      | v3_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f242])).

fof(f2034,plain,
    ( spl22_304
    | ~ spl22_307
    | spl22_316
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f1990,f1963,f2032,f2013,f2007])).

fof(f2032,plain,
    ( spl22_316
  <=> ! [X4] :
        ( ~ m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | ~ v3_tex_2(u1_struct_0(X4),sK2(sK0,sK12(u1_struct_0(sK0))))
        | v4_tex_2(X4,sK2(sK0,sK12(u1_struct_0(sK0))))
        | ~ m1_pre_topc(X4,sK2(sK0,sK12(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_316])])).

fof(f1990,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
        | ~ m1_pre_topc(X4,sK2(sK0,sK12(u1_struct_0(sK0))))
        | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
        | v4_tex_2(X4,sK2(sK0,sK12(u1_struct_0(sK0))))
        | ~ v3_tex_2(u1_struct_0(X4),sK2(sK0,sK12(u1_struct_0(sK0)))) )
    | ~ spl22_300 ),
    inference(superposition,[],[f334,f1964])).

fof(f2030,plain,
    ( spl22_304
    | ~ spl22_307
    | spl22_314
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f1989,f1963,f2028,f2013,f2007])).

fof(f2028,plain,
    ( spl22_314
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | u1_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),X3)) = X3
        | v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_314])])).

fof(f1989,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
        | u1_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),X3)) = X3 )
    | ~ spl22_300 ),
    inference(superposition,[],[f268,f1964])).

fof(f2026,plain,
    ( spl22_304
    | ~ spl22_307
    | spl22_312
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f1988,f1963,f2024,f2013,f2007])).

fof(f2024,plain,
    ( spl22_312
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | m1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),X2),sK2(sK0,sK12(u1_struct_0(sK0))))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_312])])).

fof(f1988,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
        | v1_xboole_0(X2)
        | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
        | m1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),X2),sK2(sK0,sK12(u1_struct_0(sK0)))) )
    | ~ spl22_300 ),
    inference(superposition,[],[f267,f1964])).

fof(f2022,plain,
    ( spl22_304
    | ~ spl22_307
    | spl22_310
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f1987,f1963,f2020,f2013,f2007])).

fof(f2020,plain,
    ( spl22_310
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | v1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),X1))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_310])])).

fof(f1987,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
        | v1_xboole_0(X1)
        | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
        | v1_pre_topc(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),X1)) )
    | ~ spl22_300 ),
    inference(superposition,[],[f266,f1964])).

fof(f2018,plain,
    ( spl22_304
    | ~ spl22_307
    | spl22_308
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f1986,f1963,f2016,f2013,f2007])).

fof(f2016,plain,
    ( spl22_308
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | ~ v2_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),X0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_308])])).

fof(f1986,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK2(sK0,sK12(u1_struct_0(sK0))))
        | v1_xboole_0(X0)
        | v2_struct_0(sK2(sK0,sK12(u1_struct_0(sK0))))
        | ~ v2_struct_0(sK2(sK2(sK0,sK12(u1_struct_0(sK0))),X0)) )
    | ~ spl22_300 ),
    inference(superposition,[],[f265,f1964])).

fof(f1984,plain,
    ( spl22_302
    | spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | spl22_185 ),
    inference(avatar_split_clause,[],[f1977,f1365,f1362,f1338,f990,f1982])).

fof(f1982,plain,
    ( spl22_302
  <=> u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1))))) = sK12(sK12(sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_302])])).

fof(f1365,plain,
    ( spl22_185
  <=> ~ v1_xboole_0(sK12(sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_185])])).

fof(f1977,plain,
    ( u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1))))) = sK12(sK12(sK12(sK1)))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f1976,f1363])).

fof(f1976,plain,
    ( u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))))) = sK12(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f1975,f1339])).

fof(f1975,plain,
    ( u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))))) = sK12(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_182
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f1974,f991])).

fof(f1974,plain,
    ( v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))))) = sK12(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_182
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f1956,f1366])).

fof(f1366,plain,
    ( ~ v1_xboole_0(sK12(sK12(sK1)))
    | ~ spl22_185 ),
    inference(avatar_component_clause,[],[f1365])).

fof(f1956,plain,
    ( v1_xboole_0(sK12(sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))))) = sK12(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_182 ),
    inference(superposition,[],[f823,f1363])).

fof(f1965,plain,
    ( spl22_300
    | ~ spl22_0
    | spl22_5
    | spl22_73 ),
    inference(avatar_split_clause,[],[f1958,f612,f354,f340,f1963])).

fof(f612,plain,
    ( spl22_73
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_73])])).

fof(f1958,plain,
    ( u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))) = sK12(u1_struct_0(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_73 ),
    inference(subsumption_resolution,[],[f1957,f341])).

fof(f1957,plain,
    ( u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))) = sK12(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl22_5
    | ~ spl22_73 ),
    inference(subsumption_resolution,[],[f1942,f355])).

fof(f1942,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK2(sK0,sK12(u1_struct_0(sK0)))) = sK12(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl22_73 ),
    inference(resolution,[],[f823,f613])).

fof(f613,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl22_73 ),
    inference(avatar_component_clause,[],[f612])).

fof(f1933,plain,
    ( ~ spl22_30
    | spl22_263
    | ~ spl22_272 ),
    inference(avatar_contradiction_clause,[],[f1932])).

fof(f1932,plain,
    ( $false
    | ~ spl22_30
    | ~ spl22_263
    | ~ spl22_272 ),
    inference(subsumption_resolution,[],[f1872,f592])).

fof(f592,plain,
    ( ! [X0] : m1_subset_1(sK13,k1_zfmisc_1(X0))
    | ~ spl22_30 ),
    inference(backward_demodulation,[],[f591,f294])).

fof(f294,plain,(
    ! [X0] : m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f165])).

fof(f165,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc2_subset_1)).

fof(f591,plain,
    ( ! [X0] : sK11(X0) = sK13
    | ~ spl22_30 ),
    inference(resolution,[],[f588,f295])).

fof(f295,plain,(
    ! [X0] : v1_xboole_0(sK11(X0)) ),
    inference(cnf_transformation,[],[f165])).

fof(f588,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK13 = X0 )
    | ~ spl22_30 ),
    inference(resolution,[],[f264,f446])).

fof(f446,plain,
    ( v1_xboole_0(sK13)
    | ~ spl22_30 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl22_30
  <=> v1_xboole_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_30])])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f222])).

fof(f222,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',t8_boole)).

fof(f1872,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(sK1))
    | ~ spl22_263
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1739])).

fof(f1739,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK12(sK1))),k1_zfmisc_1(sK1))
    | ~ spl22_263 ),
    inference(avatar_component_clause,[],[f1738])).

fof(f1738,plain,
    ( spl22_263
  <=> ~ m1_subset_1(sK10(k1_zfmisc_1(sK12(sK1))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_263])])).

fof(f1931,plain,
    ( ~ spl22_299
    | spl22_261
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f1871,f1825,f1732,f1929])).

fof(f1929,plain,
    ( spl22_299
  <=> ~ v3_tex_2(sK13,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_299])])).

fof(f1732,plain,
    ( spl22_261
  <=> ~ v3_tex_2(sK10(k1_zfmisc_1(sK12(sK1))),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_261])])).

fof(f1871,plain,
    ( ~ v3_tex_2(sK13,sK2(sK0,sK1))
    | ~ spl22_261
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1733])).

fof(f1733,plain,
    ( ~ v3_tex_2(sK10(k1_zfmisc_1(sK12(sK1))),sK2(sK0,sK1))
    | ~ spl22_261 ),
    inference(avatar_component_clause,[],[f1732])).

fof(f1924,plain,
    ( ~ spl22_297
    | spl22_259
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f1870,f1825,f1726,f1922])).

fof(f1922,plain,
    ( spl22_297
  <=> ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_297])])).

fof(f1726,plain,
    ( spl22_259
  <=> ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_259])])).

fof(f1870,plain,
    ( ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK2(sK0,sK1))
    | ~ spl22_259
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1727])).

fof(f1727,plain,
    ( ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1))
    | ~ spl22_259 ),
    inference(avatar_component_clause,[],[f1726])).

fof(f1917,plain,
    ( ~ spl22_295
    | spl22_257
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f1869,f1825,f1717,f1915])).

fof(f1915,plain,
    ( spl22_295
  <=> ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_295])])).

fof(f1717,plain,
    ( spl22_257
  <=> ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_257])])).

fof(f1869,plain,
    ( ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK2(sK0,sK1))
    | ~ spl22_257
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1718])).

fof(f1718,plain,
    ( ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1))
    | ~ spl22_257 ),
    inference(avatar_component_clause,[],[f1717])).

fof(f1910,plain,
    ( ~ spl22_293
    | spl22_225
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f1868,f1825,f1582,f1908])).

fof(f1908,plain,
    ( spl22_293
  <=> ~ v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK12(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_293])])).

fof(f1582,plain,
    ( spl22_225
  <=> ~ v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_225])])).

fof(f1868,plain,
    ( ~ v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK12(sK13)))
    | ~ spl22_225
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1583])).

fof(f1583,plain,
    ( ~ v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_225 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1903,plain,
    ( ~ spl22_291
    | spl22_223
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f1867,f1825,f1575,f1901])).

fof(f1901,plain,
    ( spl22_291
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK12(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_291])])).

fof(f1575,plain,
    ( spl22_223
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_223])])).

fof(f1867,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK12(sK13)))
    | ~ spl22_223
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1576])).

fof(f1576,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_223 ),
    inference(avatar_component_clause,[],[f1575])).

fof(f1896,plain,
    ( ~ spl22_289
    | ~ spl22_74
    | spl22_219
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f1889,f1825,f1559,f631,f1894])).

fof(f1894,plain,
    ( spl22_289
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_289])])).

fof(f631,plain,
    ( spl22_74
  <=> sK10(k1_zfmisc_1(sK13)) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_74])])).

fof(f1559,plain,
    ( spl22_219
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_219])])).

fof(f1889,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK13))
    | ~ spl22_74
    | ~ spl22_219
    | ~ spl22_272 ),
    inference(forward_demodulation,[],[f1866,f632])).

fof(f632,plain,
    ( sK10(k1_zfmisc_1(sK13)) = sK13
    | ~ spl22_74 ),
    inference(avatar_component_clause,[],[f631])).

fof(f1866,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13),sK10(k1_zfmisc_1(sK13))))
    | ~ spl22_219
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1560])).

fof(f1560,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))))
    | ~ spl22_219 ),
    inference(avatar_component_clause,[],[f1559])).

fof(f1888,plain,
    ( ~ spl22_287
    | spl22_205
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f1865,f1825,f1520,f1886])).

fof(f1886,plain,
    ( spl22_287
  <=> ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_287])])).

fof(f1520,plain,
    ( spl22_205
  <=> ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_205])])).

fof(f1865,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13))
    | ~ spl22_205
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1521])).

fof(f1521,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_205 ),
    inference(avatar_component_clause,[],[f1520])).

fof(f1881,plain,
    ( ~ spl22_285
    | spl22_187
    | ~ spl22_272 ),
    inference(avatar_split_clause,[],[f1864,f1825,f1397,f1879])).

fof(f1879,plain,
    ( spl22_285
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_285])])).

fof(f1397,plain,
    ( spl22_187
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_187])])).

fof(f1864,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK13))
    | ~ spl22_187
    | ~ spl22_272 ),
    inference(backward_demodulation,[],[f1826,f1398])).

fof(f1398,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_187 ),
    inference(avatar_component_clause,[],[f1397])).

fof(f1862,plain,
    ( spl22_282
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(avatar_split_clause,[],[f1820,f1354,f445,f1860])).

fof(f1860,plain,
    ( spl22_282
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_282])])).

fof(f1354,plain,
    ( spl22_180
  <=> v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_180])])).

fof(f1820,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(resolution,[],[f1355,f714])).

fof(f714,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))))))))) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f704,f604])).

fof(f604,plain,(
    ! [X0] :
      ( v1_xboole_0(sK10(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f296,f293])).

fof(f296,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f243])).

fof(f243,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',cc1_subset_1)).

fof(f704,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))))))) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f643,f604])).

fof(f643,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))))) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f626,f604])).

fof(f626,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f615,f604])).

fof(f615,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(X0)) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f604,f588])).

fof(f1355,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | ~ spl22_180 ),
    inference(avatar_component_clause,[],[f1354])).

fof(f1855,plain,
    ( spl22_280
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(avatar_split_clause,[],[f1818,f1354,f445,f1853])).

fof(f1853,plain,
    ( spl22_280
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_280])])).

fof(f1818,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(resolution,[],[f1355,f704])).

fof(f1848,plain,
    ( spl22_278
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(avatar_split_clause,[],[f1816,f1354,f445,f1846])).

fof(f1846,plain,
    ( spl22_278
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_278])])).

fof(f1816,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(resolution,[],[f1355,f643])).

fof(f1841,plain,
    ( spl22_276
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(avatar_split_clause,[],[f1814,f1354,f445,f1839])).

fof(f1839,plain,
    ( spl22_276
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_276])])).

fof(f1814,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))) = sK13
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(resolution,[],[f1355,f626])).

fof(f1834,plain,
    ( spl22_274
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(avatar_split_clause,[],[f1812,f1354,f445,f1832])).

fof(f1832,plain,
    ( spl22_274
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_274])])).

fof(f1812,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))) = sK13
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(resolution,[],[f1355,f615])).

fof(f1827,plain,
    ( spl22_272
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(avatar_split_clause,[],[f1811,f1354,f445,f1825])).

fof(f1811,plain,
    ( sK10(k1_zfmisc_1(sK12(sK1))) = sK13
    | ~ spl22_30
    | ~ spl22_180 ),
    inference(resolution,[],[f1355,f588])).

fof(f1809,plain,
    ( ~ spl22_181
    | spl22_221 ),
    inference(avatar_split_clause,[],[f1598,f1562,f1351])).

fof(f1351,plain,
    ( spl22_181
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_181])])).

fof(f1562,plain,
    ( spl22_221
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_221])])).

fof(f1598,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | ~ spl22_221 ),
    inference(resolution,[],[f1563,f604])).

fof(f1563,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_221 ),
    inference(avatar_component_clause,[],[f1562])).

fof(f1808,plain,
    ( spl22_228
    | spl22_180
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(avatar_split_clause,[],[f1610,f934,f910,f859,f1354,f1616])).

fof(f1616,plain,
    ( spl22_228
  <=> v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_228])])).

fof(f859,plain,
    ( spl22_99
  <=> ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_99])])).

fof(f910,plain,
    ( spl22_108
  <=> l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_108])])).

fof(f934,plain,
    ( spl22_114
  <=> u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) = sK12(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_114])])).

fof(f1610,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f1609,f935])).

fof(f935,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) = sK12(sK1)
    | ~ spl22_114 ),
    inference(avatar_component_clause,[],[f934])).

fof(f1609,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1608,f911])).

fof(f911,plain,
    ( l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_108 ),
    inference(avatar_component_clause,[],[f910])).

fof(f1608,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1600,f860])).

fof(f860,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99 ),
    inference(avatar_component_clause,[],[f859])).

fof(f1600,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_114 ),
    inference(superposition,[],[f734,f935])).

fof(f1807,plain,
    ( spl22_264
    | spl22_180
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(avatar_split_clause,[],[f1763,f934,f910,f859,f1354,f1769])).

fof(f1769,plain,
    ( spl22_264
  <=> m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_264])])).

fof(f1763,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f1762,f935])).

fof(f1762,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1761,f911])).

fof(f1761,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1750,f860])).

fof(f1750,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_114 ),
    inference(superposition,[],[f760,f935])).

fof(f1806,plain,
    ( ~ spl22_108
    | spl22_205
    | ~ spl22_264 ),
    inference(avatar_contradiction_clause,[],[f1805])).

fof(f1805,plain,
    ( $false
    | ~ spl22_108
    | ~ spl22_205
    | ~ spl22_264 ),
    inference(subsumption_resolution,[],[f1804,f1521])).

fof(f1804,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_108
    | ~ spl22_264 ),
    inference(subsumption_resolution,[],[f1785,f911])).

fof(f1785,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_264 ),
    inference(resolution,[],[f1770,f273])).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f235])).

fof(f235,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f112])).

fof(f112,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',dt_m1_pre_topc)).

fof(f1770,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_264 ),
    inference(avatar_component_clause,[],[f1769])).

fof(f1803,plain,
    ( spl22_268
    | ~ spl22_104
    | ~ spl22_108
    | ~ spl22_264 ),
    inference(avatar_split_clause,[],[f1802,f1769,f910,f893,f1792])).

fof(f1792,plain,
    ( spl22_268
  <=> v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_268])])).

fof(f893,plain,
    ( spl22_104
  <=> v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_104])])).

fof(f1802,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_104
    | ~ spl22_108
    | ~ spl22_264 ),
    inference(subsumption_resolution,[],[f1801,f894])).

fof(f894,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_104 ),
    inference(avatar_component_clause,[],[f893])).

fof(f1801,plain,
    ( ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_108
    | ~ spl22_264 ),
    inference(subsumption_resolution,[],[f1784,f911])).

fof(f1784,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_264 ),
    inference(resolution,[],[f1770,f271])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f233])).

fof(f233,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f232])).

fof(f232,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',cc1_pre_topc)).

fof(f1800,plain,
    ( spl22_268
    | ~ spl22_271
    | spl22_99
    | ~ spl22_108
    | ~ spl22_264 ),
    inference(avatar_split_clause,[],[f1787,f1769,f910,f859,f1798,f1792])).

fof(f1787,plain,
    ( ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_264 ),
    inference(subsumption_resolution,[],[f1786,f860])).

fof(f1786,plain,
    ( v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_108
    | ~ spl22_264 ),
    inference(subsumption_resolution,[],[f1783,f911])).

fof(f1783,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_264 ),
    inference(resolution,[],[f1770,f303])).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f246])).

fof(f246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f245])).

fof(f245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',cc14_tex_2)).

fof(f1782,plain,
    ( spl22_266
    | spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | spl22_197 ),
    inference(avatar_split_clause,[],[f1775,f1460,f1362,f1338,f990,f1780])).

fof(f1780,plain,
    ( spl22_266
  <=> m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_266])])).

fof(f1775,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_197 ),
    inference(subsumption_resolution,[],[f1774,f1461])).

fof(f1774,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK12(sK1)))))
    | m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(forward_demodulation,[],[f1773,f1363])).

fof(f1773,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1772,f1339])).

fof(f1772,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1751,f991])).

fof(f1751,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_182 ),
    inference(superposition,[],[f760,f1363])).

fof(f1771,plain,
    ( spl22_264
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_181 ),
    inference(avatar_split_clause,[],[f1764,f1351,f934,f910,f859,f1769])).

fof(f1764,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_181 ),
    inference(subsumption_resolution,[],[f1763,f1352])).

fof(f1352,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | ~ spl22_181 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f1743,plain,
    ( spl22_11
    | spl22_247 ),
    inference(avatar_contradiction_clause,[],[f1742])).

fof(f1742,plain,
    ( $false
    | ~ spl22_11
    | ~ spl22_247 ),
    inference(subsumption_resolution,[],[f1741,f376])).

fof(f376,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl22_11 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl22_11
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_11])])).

fof(f1741,plain,
    ( v1_xboole_0(sK1)
    | ~ spl22_247 ),
    inference(resolution,[],[f1687,f297])).

fof(f1687,plain,
    ( ~ m1_subset_1(sK12(sK1),k1_zfmisc_1(sK1))
    | ~ spl22_247 ),
    inference(avatar_component_clause,[],[f1686])).

fof(f1686,plain,
    ( spl22_247
  <=> ~ m1_subset_1(sK12(sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_247])])).

fof(f1740,plain,
    ( spl22_256
    | ~ spl22_259
    | ~ spl22_261
    | ~ spl22_263
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_178 ),
    inference(avatar_split_clause,[],[f1715,f1348,f820,f800,f729,f1738,f1732,f1726,f1720])).

fof(f1720,plain,
    ( spl22_256
  <=> v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_256])])).

fof(f1348,plain,
    ( spl22_178
  <=> u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) = sK10(k1_zfmisc_1(sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_178])])).

fof(f1715,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK12(sK1))),k1_zfmisc_1(sK1))
    | ~ v3_tex_2(sK10(k1_zfmisc_1(sK12(sK1))),sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_178 ),
    inference(forward_demodulation,[],[f1641,f1349])).

fof(f1349,plain,
    ( u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) = sK10(k1_zfmisc_1(sK12(sK1)))
    | ~ spl22_178 ),
    inference(avatar_component_clause,[],[f1348])).

fof(f1641,plain,
    ( ~ v3_tex_2(sK10(k1_zfmisc_1(sK12(sK1))),sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK2(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_178 ),
    inference(superposition,[],[f1204,f1349])).

fof(f1714,plain,
    ( spl22_248
    | ~ spl22_251
    | ~ spl22_253
    | ~ spl22_255
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_182 ),
    inference(avatar_split_clause,[],[f1689,f1362,f820,f800,f729,f1712,f1706,f1700,f1694])).

fof(f1694,plain,
    ( spl22_248
  <=> v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_248])])).

fof(f1700,plain,
    ( spl22_251
  <=> ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_251])])).

fof(f1706,plain,
    ( spl22_253
  <=> ~ v3_tex_2(sK12(sK12(sK1)),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_253])])).

fof(f1712,plain,
    ( spl22_255
  <=> ~ m1_subset_1(sK12(sK12(sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_255])])).

fof(f1689,plain,
    ( ~ m1_subset_1(sK12(sK12(sK1)),k1_zfmisc_1(sK1))
    | ~ v3_tex_2(sK12(sK12(sK1)),sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK0,sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_182 ),
    inference(forward_demodulation,[],[f1640,f1363])).

fof(f1640,plain,
    ( ~ v3_tex_2(sK12(sK12(sK1)),sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_182 ),
    inference(superposition,[],[f1204,f1363])).

fof(f1688,plain,
    ( spl22_242
    | ~ spl22_245
    | ~ spl22_247
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_102
    | ~ spl22_114 ),
    inference(avatar_split_clause,[],[f1669,f934,f881,f820,f800,f729,f1686,f1680,f1674])).

fof(f1674,plain,
    ( spl22_242
  <=> v4_tex_2(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_242])])).

fof(f1680,plain,
    ( spl22_245
  <=> ~ v3_tex_2(sK12(sK1),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_245])])).

fof(f881,plain,
    ( spl22_102
  <=> m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_102])])).

fof(f1669,plain,
    ( ~ m1_subset_1(sK12(sK1),k1_zfmisc_1(sK1))
    | ~ v3_tex_2(sK12(sK1),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_102
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f1668,f935])).

fof(f1668,plain,
    ( ~ v3_tex_2(sK12(sK1),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_102
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1639,f882])).

fof(f882,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ spl22_102 ),
    inference(avatar_component_clause,[],[f881])).

fof(f1639,plain,
    ( ~ v3_tex_2(sK12(sK1),sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_114 ),
    inference(superposition,[],[f1204,f935])).

fof(f1667,plain,
    ( spl22_234
    | ~ spl22_237
    | ~ spl22_239
    | ~ spl22_241
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f1642,f820,f800,f729,f1665,f1659,f1653,f1647])).

fof(f1647,plain,
    ( spl22_234
  <=> v4_tex_2(sK2(sK0,sK1),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_234])])).

fof(f1653,plain,
    ( spl22_237
  <=> ~ m1_pre_topc(sK2(sK0,sK1),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_237])])).

fof(f1659,plain,
    ( spl22_239
  <=> ~ v3_tex_2(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_239])])).

fof(f1665,plain,
    ( spl22_241
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_241])])).

fof(f1642,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ v3_tex_2(sK1,sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK1),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK0,sK1),sK2(sK0,sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f1638,f821])).

fof(f1638,plain,
    ( ~ v3_tex_2(sK1,sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK1),sK2(sK0,sK1))
    | v4_tex_2(sK2(sK0,sK1),sK2(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(superposition,[],[f1204,f821])).

fof(f1637,plain,
    ( ~ spl22_233
    | spl22_147
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1630,f1152,f1118,f1635])).

fof(f1635,plain,
    ( spl22_233
  <=> ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13)),sK2(sK2(sK0,sK1),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_233])])).

fof(f1118,plain,
    ( spl22_147
  <=> ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_147])])).

fof(f1152,plain,
    ( spl22_148
  <=> sK10(k1_zfmisc_1(sK1)) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_148])])).

fof(f1630,plain,
    ( ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13)),sK2(sK2(sK0,sK1),sK13))
    | ~ spl22_147
    | ~ spl22_148 ),
    inference(forward_demodulation,[],[f1119,f1153])).

fof(f1153,plain,
    ( sK10(k1_zfmisc_1(sK1)) = sK13
    | ~ spl22_148 ),
    inference(avatar_component_clause,[],[f1152])).

fof(f1119,plain,
    ( ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_147 ),
    inference(avatar_component_clause,[],[f1118])).

fof(f1629,plain,
    ( spl22_230
    | spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | spl22_197 ),
    inference(avatar_split_clause,[],[f1622,f1460,f1362,f1338,f990,f1627])).

fof(f1627,plain,
    ( spl22_230
  <=> v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_230])])).

fof(f1622,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_197 ),
    inference(subsumption_resolution,[],[f1621,f1461])).

fof(f1621,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK12(sK1)))))
    | v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(forward_demodulation,[],[f1620,f1363])).

fof(f1620,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1619,f1339])).

fof(f1619,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1601,f991])).

fof(f1601,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_182 ),
    inference(superposition,[],[f734,f1363])).

fof(f1618,plain,
    ( spl22_228
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_181 ),
    inference(avatar_split_clause,[],[f1611,f1351,f934,f910,f859,f1616])).

fof(f1611,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_181 ),
    inference(subsumption_resolution,[],[f1610,f1352])).

fof(f1597,plain,
    ( ~ spl22_205
    | spl22_226
    | ~ spl22_178
    | spl22_181
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1590,f1397,f1351,f1348,f1595,f1520])).

fof(f1595,plain,
    ( spl22_226
  <=> m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_226])])).

fof(f1590,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178
    | ~ spl22_181
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1589,f1352])).

fof(f1589,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(forward_demodulation,[],[f1588,f1349])).

fof(f1588,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1512,f1398])).

fof(f1512,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_178 ),
    inference(superposition,[],[f773,f1349])).

fof(f1587,plain,
    ( ~ spl22_205
    | spl22_224
    | ~ spl22_178
    | spl22_181
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1580,f1397,f1351,f1348,f1585,f1520])).

fof(f1585,plain,
    ( spl22_224
  <=> v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_224])])).

fof(f1580,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178
    | ~ spl22_181
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1579,f1352])).

fof(f1579,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(forward_demodulation,[],[f1578,f1349])).

fof(f1578,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1511,f1398])).

fof(f1511,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_178 ),
    inference(superposition,[],[f747,f1349])).

fof(f1577,plain,
    ( ~ spl22_205
    | ~ spl22_223
    | ~ spl22_178
    | spl22_181
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1570,f1397,f1351,f1348,f1575,f1520])).

fof(f1570,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178
    | ~ spl22_181
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1569,f1352])).

fof(f1569,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(forward_demodulation,[],[f1568,f1349])).

fof(f1568,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1510,f1398])).

fof(f1510,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK12(sK10(k1_zfmisc_1(sK12(sK1))))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ spl22_178 ),
    inference(superposition,[],[f732,f1349])).

fof(f1567,plain,
    ( ~ spl22_205
    | ~ spl22_219
    | spl22_220
    | ~ spl22_178
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1554,f1397,f1348,f1565,f1559,f1520])).

fof(f1565,plain,
    ( spl22_220
  <=> v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_220])])).

fof(f1554,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1))))))
    | ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(forward_demodulation,[],[f1553,f1349])).

fof(f1553,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1509,f1398])).

fof(f1509,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_178 ),
    inference(superposition,[],[f719,f1349])).

fof(f1551,plain,
    ( ~ spl22_205
    | spl22_216
    | ~ spl22_178
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1547,f1397,f1348,f1549,f1520])).

fof(f1549,plain,
    ( spl22_216
  <=> ! [X6] :
        ( ~ m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | v3_tex_2(u1_struct_0(X6),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ v4_tex_2(X6,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ m1_pre_topc(X6,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_216])])).

fof(f1547,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ m1_pre_topc(X6,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ v4_tex_2(X6,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v3_tex_2(u1_struct_0(X6),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) )
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1507,f1398])).

fof(f1507,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ m1_pre_topc(X6,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ v4_tex_2(X6,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v3_tex_2(u1_struct_0(X6),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) )
    | ~ spl22_178 ),
    inference(superposition,[],[f335,f1349])).

fof(f1545,plain,
    ( ~ spl22_205
    | spl22_214
    | ~ spl22_178
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1541,f1397,f1348,f1543,f1520])).

fof(f1543,plain,
    ( spl22_214
  <=> ! [X4] :
        ( ~ m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ v3_tex_2(u1_struct_0(X4),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v4_tex_2(X4,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ m1_pre_topc(X4,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_214])])).

fof(f1541,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ m1_pre_topc(X4,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v4_tex_2(X4,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ v3_tex_2(u1_struct_0(X4),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) )
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1505,f1398])).

fof(f1505,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ m1_pre_topc(X4,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v4_tex_2(X4,sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ v3_tex_2(u1_struct_0(X4),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) )
    | ~ spl22_178 ),
    inference(superposition,[],[f334,f1349])).

fof(f1540,plain,
    ( ~ spl22_205
    | spl22_212
    | ~ spl22_178
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1536,f1397,f1348,f1538,f1520])).

fof(f1538,plain,
    ( spl22_212
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X3)) = X3
        | v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_212])])).

fof(f1536,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X3)
        | u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X3)) = X3 )
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1504,f1398])).

fof(f1504,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | u1_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X3)) = X3 )
    | ~ spl22_178 ),
    inference(superposition,[],[f268,f1349])).

fof(f1535,plain,
    ( ~ spl22_205
    | spl22_210
    | ~ spl22_178
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1531,f1397,f1348,f1533,f1520])).

fof(f1533,plain,
    ( spl22_210
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X2),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_210])])).

fof(f1531,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X2)
        | m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X2),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) )
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1503,f1398])).

fof(f1503,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X2)
        | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X2),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) )
    | ~ spl22_178 ),
    inference(superposition,[],[f267,f1349])).

fof(f1530,plain,
    ( ~ spl22_205
    | spl22_208
    | ~ spl22_178
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1526,f1397,f1348,f1528,f1520])).

fof(f1528,plain,
    ( spl22_208
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X1))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_208])])).

fof(f1526,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X1)
        | v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X1)) )
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1502,f1398])).

fof(f1502,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X1)
        | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X1)) )
    | ~ spl22_178 ),
    inference(superposition,[],[f266,f1349])).

fof(f1525,plain,
    ( ~ spl22_205
    | spl22_206
    | ~ spl22_178
    | spl22_187 ),
    inference(avatar_split_clause,[],[f1515,f1397,f1348,f1523,f1520])).

fof(f1523,plain,
    ( spl22_206
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_206])])).

fof(f1515,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X0)
        | ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X0)) )
    | ~ spl22_178
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f1501,f1398])).

fof(f1501,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | v1_xboole_0(X0)
        | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
        | ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))),X0)) )
    | ~ spl22_178 ),
    inference(superposition,[],[f265,f1349])).

fof(f1498,plain,
    ( spl22_202
    | spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | spl22_185 ),
    inference(avatar_split_clause,[],[f1491,f1365,f1362,f1338,f990,f1496])).

fof(f1496,plain,
    ( spl22_202
  <=> m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_202])])).

fof(f1491,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f1490,f1366])).

fof(f1490,plain,
    ( v1_xboole_0(sK12(sK12(sK1)))
    | m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(forward_demodulation,[],[f1489,f1363])).

fof(f1489,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1488,f1339])).

fof(f1488,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1413,f991])).

fof(f1413,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))),sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_182 ),
    inference(superposition,[],[f773,f1363])).

fof(f1487,plain,
    ( spl22_200
    | spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | spl22_185 ),
    inference(avatar_split_clause,[],[f1480,f1365,f1362,f1338,f990,f1485])).

fof(f1485,plain,
    ( spl22_200
  <=> v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_200])])).

fof(f1480,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f1479,f1366])).

fof(f1479,plain,
    ( v1_xboole_0(sK12(sK12(sK1)))
    | v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(forward_demodulation,[],[f1478,f1363])).

fof(f1478,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1477,f1339])).

fof(f1477,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1412,f991])).

fof(f1412,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_182 ),
    inference(superposition,[],[f747,f1363])).

fof(f1476,plain,
    ( ~ spl22_199
    | spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | spl22_185 ),
    inference(avatar_split_clause,[],[f1469,f1365,f1362,f1338,f990,f1474])).

fof(f1474,plain,
    ( spl22_199
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_199])])).

fof(f1469,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f1468,f1366])).

fof(f1468,plain,
    ( v1_xboole_0(sK12(sK12(sK1)))
    | ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(forward_demodulation,[],[f1467,f1363])).

fof(f1467,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1466,f1339])).

fof(f1466,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_125
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1411,f991])).

fof(f1411,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK12(sK12(sK12(sK1)))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))
    | ~ spl22_182 ),
    inference(superposition,[],[f732,f1363])).

fof(f1465,plain,
    ( ~ spl22_195
    | spl22_196
    | spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(avatar_split_clause,[],[f1452,f1362,f1338,f990,f1463,f1457])).

fof(f1457,plain,
    ( spl22_195
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_195])])).

fof(f1463,plain,
    ( spl22_196
  <=> v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK12(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_196])])).

fof(f1452,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK12(sK1)))))
    | ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(forward_demodulation,[],[f1451,f1363])).

fof(f1451,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | ~ spl22_125
    | ~ spl22_176
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1450,f1339])).

fof(f1450,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_125
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1410,f991])).

fof(f1410,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK10(k1_zfmisc_1(sK12(sK12(sK1))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))))))
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_182 ),
    inference(superposition,[],[f719,f1363])).

fof(f1435,plain,
    ( ~ spl22_189
    | ~ spl22_191
    | ~ spl22_193
    | spl22_125
    | ~ spl22_126
    | ~ spl22_182 ),
    inference(avatar_split_clause,[],[f1416,f1362,f1001,f990,f1433,f1427,f1421])).

fof(f1421,plain,
    ( spl22_189
  <=> ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_189])])).

fof(f1427,plain,
    ( spl22_191
  <=> ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_191])])).

fof(f1433,plain,
    ( spl22_193
  <=> sK1 != sK12(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_193])])).

fof(f1001,plain,
    ( spl22_126
  <=> v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_126])])).

fof(f1416,plain,
    ( sK1 != sK12(sK12(sK1))
    | ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK1),sK0)
    | ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK1),sK0)
    | ~ spl22_125
    | ~ spl22_126
    | ~ spl22_182 ),
    inference(inner_rewriting,[],[f1415])).

fof(f1415,plain,
    ( sK1 != sK12(sK12(sK1))
    | ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK0)
    | ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK0)
    | ~ spl22_125
    | ~ spl22_126
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1414,f991])).

fof(f1414,plain,
    ( sK1 != sK12(sK12(sK1))
    | ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK0)
    | ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK0)
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_126
    | ~ spl22_182 ),
    inference(subsumption_resolution,[],[f1401,f1002])).

fof(f1002,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_126 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f1401,plain,
    ( sK1 != sK12(sK12(sK1))
    | ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK0)
    | ~ v4_tex_2(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK0)
    | v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_182 ),
    inference(superposition,[],[f257,f1363])).

fof(f257,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK1
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v4_tex_2(X2,sK0)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f224])).

fof(f224,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f223])).

fof(f223,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',t53_tex_2)).

fof(f1399,plain,
    ( ~ spl22_187
    | spl22_180
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(avatar_split_clause,[],[f1392,f934,f910,f859,f1354,f1397])).

fof(f1392,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f1391,f935])).

fof(f1391,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1390,f911])).

fof(f1390,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1386,f860])).

fof(f1386,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1)))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_114 ),
    inference(superposition,[],[f719,f935])).

fof(f1384,plain,
    ( spl22_117
    | ~ spl22_184 ),
    inference(avatar_contradiction_clause,[],[f1383])).

fof(f1383,plain,
    ( $false
    | ~ spl22_117
    | ~ spl22_184 ),
    inference(subsumption_resolution,[],[f1371,f938])).

fof(f938,plain,
    ( ~ v1_xboole_0(sK12(sK1))
    | ~ spl22_117 ),
    inference(avatar_component_clause,[],[f937])).

fof(f937,plain,
    ( spl22_117
  <=> ~ v1_xboole_0(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_117])])).

fof(f1371,plain,
    ( v1_xboole_0(sK12(sK1))
    | ~ spl22_184 ),
    inference(resolution,[],[f1369,f298])).

fof(f1369,plain,
    ( v1_xboole_0(sK12(sK12(sK1)))
    | ~ spl22_184 ),
    inference(avatar_component_clause,[],[f1368])).

fof(f1368,plain,
    ( spl22_184
  <=> v1_xboole_0(sK12(sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_184])])).

fof(f1370,plain,
    ( spl22_182
    | spl22_184
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_117 ),
    inference(avatar_split_clause,[],[f1357,f937,f934,f910,f859,f1368,f1362])).

fof(f1357,plain,
    ( v1_xboole_0(sK12(sK12(sK1)))
    | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) = sK12(sK12(sK1))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f1342,f938])).

fof(f1342,plain,
    ( v1_xboole_0(sK12(sK12(sK1)))
    | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) = sK12(sK12(sK1))
    | v1_xboole_0(sK12(sK1))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(resolution,[],[f1044,f297])).

fof(f1044,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK12(sK1)))
        | v1_xboole_0(X3)
        | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),X3)) = X3 )
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1043,f860])).

fof(f1043,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK12(sK1)))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
        | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),X3)) = X3 )
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1033,f911])).

fof(f1033,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK12(sK1)))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
        | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),X3)) = X3 )
    | ~ spl22_114 ),
    inference(superposition,[],[f268,f935])).

fof(f1356,plain,
    ( spl22_178
    | spl22_180
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(avatar_split_clause,[],[f1341,f934,f910,f859,f1354,f1348])).

fof(f1341,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK12(sK1))))
    | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK10(k1_zfmisc_1(sK12(sK1))))) = sK10(k1_zfmisc_1(sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(resolution,[],[f1044,f293])).

fof(f1340,plain,
    ( spl22_176
    | ~ spl22_108
    | ~ spl22_128 ),
    inference(avatar_split_clause,[],[f1333,f1012,f910,f1338])).

fof(f1012,plain,
    ( spl22_128
  <=> m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_128])])).

fof(f1333,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_108
    | ~ spl22_128 ),
    inference(subsumption_resolution,[],[f1314,f911])).

fof(f1314,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_128 ),
    inference(resolution,[],[f1013,f273])).

fof(f1013,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_128 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f1332,plain,
    ( spl22_172
    | ~ spl22_104
    | ~ spl22_108
    | ~ spl22_128 ),
    inference(avatar_split_clause,[],[f1331,f1012,f910,f893,f1321])).

fof(f1321,plain,
    ( spl22_172
  <=> v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_172])])).

fof(f1331,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_104
    | ~ spl22_108
    | ~ spl22_128 ),
    inference(subsumption_resolution,[],[f1330,f894])).

fof(f1330,plain,
    ( ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_108
    | ~ spl22_128 ),
    inference(subsumption_resolution,[],[f1313,f911])).

fof(f1313,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_128 ),
    inference(resolution,[],[f1013,f271])).

fof(f1329,plain,
    ( spl22_172
    | ~ spl22_175
    | spl22_99
    | ~ spl22_108
    | ~ spl22_128 ),
    inference(avatar_split_clause,[],[f1316,f1012,f910,f859,f1327,f1321])).

fof(f1327,plain,
    ( spl22_175
  <=> ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_175])])).

fof(f1316,plain,
    ( ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_128 ),
    inference(subsumption_resolution,[],[f1315,f860])).

fof(f1315,plain,
    ( v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_108
    | ~ spl22_128 ),
    inference(subsumption_resolution,[],[f1312,f911])).

fof(f1312,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ v1_tdlat_3(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_128 ),
    inference(resolution,[],[f1013,f303])).

fof(f1295,plain,
    ( ~ spl22_171
    | spl22_111
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1288,f1152,f917,f1293])).

fof(f1293,plain,
    ( spl22_171
  <=> u1_struct_0(sK2(sK2(sK0,sK1),sK13)) != sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_171])])).

fof(f917,plain,
    ( spl22_111
  <=> u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) != sK10(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_111])])).

fof(f1288,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK1),sK13)) != sK13
    | ~ spl22_111
    | ~ spl22_148 ),
    inference(forward_demodulation,[],[f918,f1153])).

fof(f918,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) != sK10(k1_zfmisc_1(sK1))
    | ~ spl22_111 ),
    inference(avatar_component_clause,[],[f917])).

fof(f1268,plain,
    ( ~ spl22_169
    | spl22_133
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1261,f1152,f1079,f1266])).

fof(f1266,plain,
    ( spl22_169
  <=> ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_169])])).

fof(f1079,plain,
    ( spl22_133
  <=> ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_133])])).

fof(f1261,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK13))
    | ~ spl22_133
    | ~ spl22_148 ),
    inference(forward_demodulation,[],[f1080,f1153])).

fof(f1080,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_133 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f1260,plain,
    ( ~ spl22_167
    | spl22_131
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1253,f1152,f1070,f1258])).

fof(f1258,plain,
    ( spl22_167
  <=> ~ v2_struct_0(sK2(sK2(sK0,sK1),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_167])])).

fof(f1070,plain,
    ( spl22_131
  <=> ~ v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_131])])).

fof(f1253,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK13))
    | ~ spl22_131
    | ~ spl22_148 ),
    inference(forward_demodulation,[],[f1071,f1153])).

fof(f1071,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_131 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1250,plain,
    ( ~ spl22_165
    | spl22_145
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1234,f1152,f1109,f1248])).

fof(f1248,plain,
    ( spl22_165
  <=> ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_165])])).

fof(f1109,plain,
    ( spl22_145
  <=> ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_145])])).

fof(f1234,plain,
    ( ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13)))
    | ~ spl22_145
    | ~ spl22_148 ),
    inference(backward_demodulation,[],[f1153,f1110])).

fof(f1110,plain,
    ( ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_145 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1243,plain,
    ( ~ spl22_163
    | spl22_143
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1233,f1152,f1103,f1241])).

fof(f1241,plain,
    ( spl22_163
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_163])])).

fof(f1103,plain,
    ( spl22_143
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_143])])).

fof(f1233,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13)))
    | ~ spl22_143
    | ~ spl22_148 ),
    inference(backward_demodulation,[],[f1153,f1104])).

fof(f1104,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_143 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f1231,plain,
    ( spl22_158
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1225,f926,f445,f1187])).

fof(f1187,plain,
    ( spl22_158
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_158])])).

fof(f926,plain,
    ( spl22_112
  <=> v1_xboole_0(sK10(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_112])])).

fof(f1225,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f714])).

fof(f927,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ spl22_112 ),
    inference(avatar_component_clause,[],[f926])).

fof(f1230,plain,
    ( spl22_156
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1223,f926,f445,f1180])).

fof(f1180,plain,
    ( spl22_156
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_156])])).

fof(f1223,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f704])).

fof(f1229,plain,
    ( spl22_154
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1221,f926,f445,f1173])).

fof(f1173,plain,
    ( spl22_154
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_154])])).

fof(f1221,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f643])).

fof(f1228,plain,
    ( spl22_152
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1219,f926,f445,f1166])).

fof(f1166,plain,
    ( spl22_152
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_152])])).

fof(f1219,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f626])).

fof(f1227,plain,
    ( spl22_150
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1217,f926,f445,f1159])).

fof(f1159,plain,
    ( spl22_150
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_150])])).

fof(f1217,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f615])).

fof(f1226,plain,
    ( spl22_148
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1216,f926,f445,f1152])).

fof(f1216,plain,
    ( sK10(k1_zfmisc_1(sK1)) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f588])).

fof(f1214,plain,
    ( spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | spl22_113
    | ~ spl22_130 ),
    inference(avatar_contradiction_clause,[],[f1213])).

fof(f1213,plain,
    ( $false
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_113
    | ~ spl22_130 ),
    inference(subsumption_resolution,[],[f1212,f293])).

fof(f1212,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_113
    | ~ spl22_130 ),
    inference(subsumption_resolution,[],[f1211,f924])).

fof(f924,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ spl22_113 ),
    inference(avatar_component_clause,[],[f923])).

fof(f923,plain,
    ( spl22_113
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_113])])).

fof(f1211,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_130 ),
    inference(resolution,[],[f1074,f844])).

fof(f844,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK2(sK2(sK0,sK1),X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f843,f730])).

fof(f843,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v1_xboole_0(X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ v2_struct_0(sK2(sK2(sK0,sK1),X0)) )
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f825,f801])).

fof(f825,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | v1_xboole_0(X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ v2_struct_0(sK2(sK2(sK0,sK1),X0)) )
    | ~ spl22_94 ),
    inference(superposition,[],[f265,f821])).

fof(f1074,plain,
    ( v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_130 ),
    inference(avatar_component_clause,[],[f1073])).

fof(f1073,plain,
    ( spl22_130
  <=> v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_130])])).

fof(f1210,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_160
    | ~ spl22_110 ),
    inference(avatar_split_clause,[],[f1199,f920,f1208,f1079,f1073])).

fof(f1208,plain,
    ( spl22_160
  <=> ! [X2] :
        ( ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ v3_tex_2(u1_struct_0(X2),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v4_tex_2(X2,sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ m1_pre_topc(X2,sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_160])])).

fof(f920,plain,
    ( spl22_110
  <=> u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) = sK10(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_110])])).

fof(f1199,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ m1_pre_topc(X2,sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v4_tex_2(X2,sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ v3_tex_2(u1_struct_0(X2),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) )
    | ~ spl22_110 ),
    inference(superposition,[],[f334,f921])).

fof(f921,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) = sK10(k1_zfmisc_1(sK1))
    | ~ spl22_110 ),
    inference(avatar_component_clause,[],[f920])).

fof(f1192,plain,
    ( ~ spl22_133
    | spl22_130
    | spl22_146
    | spl22_112
    | ~ spl22_110 ),
    inference(avatar_split_clause,[],[f1115,f920,f926,f1121,f1073,f1079])).

fof(f1121,plain,
    ( spl22_146
  <=> m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_146])])).

fof(f1115,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1067,f921])).

fof(f1067,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_110 ),
    inference(superposition,[],[f773,f921])).

fof(f1191,plain,
    ( ~ spl22_133
    | spl22_130
    | spl22_112
    | ~ spl22_110
    | spl22_145 ),
    inference(avatar_split_clause,[],[f1190,f1109,f920,f926,f1073,f1079])).

fof(f1190,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_110
    | ~ spl22_145 ),
    inference(subsumption_resolution,[],[f1106,f1110])).

fof(f1106,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1066,f921])).

fof(f1066,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_110 ),
    inference(superposition,[],[f747,f921])).

fof(f1189,plain,
    ( spl22_158
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1147,f926,f445,f1187])).

fof(f1147,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f714])).

fof(f1182,plain,
    ( spl22_156
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1145,f926,f445,f1180])).

fof(f1145,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f704])).

fof(f1175,plain,
    ( spl22_154
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1143,f926,f445,f1173])).

fof(f1143,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f643])).

fof(f1168,plain,
    ( spl22_152
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1141,f926,f445,f1166])).

fof(f1141,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f626])).

fof(f1161,plain,
    ( spl22_150
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1139,f926,f445,f1159])).

fof(f1139,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f615])).

fof(f1154,plain,
    ( spl22_148
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f1138,f926,f445,f1152])).

fof(f1138,plain,
    ( sK10(k1_zfmisc_1(sK1)) = sK13
    | ~ spl22_30
    | ~ spl22_112 ),
    inference(resolution,[],[f927,f588])).

fof(f1136,plain,
    ( spl22_112
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | spl22_133 ),
    inference(avatar_split_clause,[],[f1133,f1079,f820,f800,f729,f926])).

fof(f1133,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_133 ),
    inference(subsumption_resolution,[],[f1132,f293])).

fof(f1132,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))
    | v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_133 ),
    inference(resolution,[],[f1131,f1080])).

fof(f1131,plain,
    ( ! [X2] :
        ( l1_pre_topc(sK2(sK2(sK0,sK1),X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | v1_xboole_0(X2) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1126,f801])).

fof(f1126,plain,
    ( ! [X2] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | l1_pre_topc(sK2(sK2(sK0,sK1),X2)) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(resolution,[],[f848,f273])).

fof(f848,plain,
    ( ! [X2] :
        ( m1_pre_topc(sK2(sK2(sK0,sK1),X2),sK2(sK0,sK1))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK1)) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f847,f730])).

fof(f847,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | v1_xboole_0(X2)
        | v2_struct_0(sK2(sK0,sK1))
        | m1_pre_topc(sK2(sK2(sK0,sK1),X2),sK2(sK0,sK1)) )
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f827,f801])).

fof(f827,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | v1_xboole_0(X2)
        | v2_struct_0(sK2(sK0,sK1))
        | m1_pre_topc(sK2(sK2(sK0,sK1),X2),sK2(sK0,sK1)) )
    | ~ spl22_94 ),
    inference(superposition,[],[f267,f821])).

fof(f1135,plain,
    ( spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | spl22_113
    | spl22_133 ),
    inference(avatar_contradiction_clause,[],[f1134])).

fof(f1134,plain,
    ( $false
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_113
    | ~ spl22_133 ),
    inference(subsumption_resolution,[],[f1133,f924])).

fof(f1123,plain,
    ( ~ spl22_133
    | spl22_130
    | spl22_146
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1116,f923,f920,f1121,f1073,f1079])).

fof(f1116,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1115,f924])).

fof(f1114,plain,
    ( ~ spl22_133
    | spl22_130
    | spl22_144
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1107,f923,f920,f1112,f1073,f1079])).

fof(f1112,plain,
    ( spl22_144
  <=> v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_144])])).

fof(f1107,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1106,f924])).

fof(f1105,plain,
    ( ~ spl22_133
    | spl22_130
    | ~ spl22_143
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1098,f923,f920,f1103,f1073,f1079])).

fof(f1098,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1097,f924])).

fof(f1097,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1065,f921])).

fof(f1065,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_110 ),
    inference(superposition,[],[f732,f921])).

fof(f1096,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_140
    | ~ spl22_110 ),
    inference(avatar_split_clause,[],[f1064,f920,f1094,f1079,f1073])).

fof(f1094,plain,
    ( spl22_140
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X3)) = X3
        | v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_140])])).

fof(f1064,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X3)) = X3 )
    | ~ spl22_110 ),
    inference(superposition,[],[f268,f921])).

fof(f1092,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_138
    | ~ spl22_110 ),
    inference(avatar_split_clause,[],[f1063,f920,f1090,f1079,f1073])).

fof(f1090,plain,
    ( spl22_138
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_138])])).

fof(f1063,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X2)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) )
    | ~ spl22_110 ),
    inference(superposition,[],[f267,f921])).

fof(f1088,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_136
    | ~ spl22_110 ),
    inference(avatar_split_clause,[],[f1062,f920,f1086,f1079,f1073])).

fof(f1086,plain,
    ( spl22_136
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X1))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_136])])).

fof(f1062,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X1)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X1)) )
    | ~ spl22_110 ),
    inference(superposition,[],[f266,f921])).

fof(f1084,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_134
    | ~ spl22_110 ),
    inference(avatar_split_clause,[],[f1061,f920,f1082,f1079,f1073])).

fof(f1082,plain,
    ( spl22_134
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_134])])).

fof(f1061,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X0)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X0)) )
    | ~ spl22_110 ),
    inference(superposition,[],[f265,f921])).

fof(f1059,plain,
    ( spl22_128
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_117 ),
    inference(avatar_split_clause,[],[f1058,f937,f934,f910,f859,f1012])).

fof(f1058,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f1057,f938])).

fof(f1057,plain,
    ( v1_xboole_0(sK12(sK1))
    | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f1056,f935])).

fof(f1056,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1055,f911])).

fof(f1055,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1036,f860])).

fof(f1036,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_114 ),
    inference(superposition,[],[f773,f935])).

fof(f1054,plain,
    ( spl22_126
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_117 ),
    inference(avatar_split_clause,[],[f1053,f937,f934,f910,f859,f1001])).

fof(f1053,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f1052,f938])).

fof(f1052,plain,
    ( v1_xboole_0(sK12(sK1))
    | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f1051,f935])).

fof(f1051,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1050,f911])).

fof(f1050,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1035,f860])).

fof(f1035,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_114 ),
    inference(superposition,[],[f747,f935])).

fof(f1049,plain,
    ( ~ spl22_125
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_117 ),
    inference(avatar_split_clause,[],[f1048,f937,f934,f910,f859,f990])).

fof(f1048,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f1047,f938])).

fof(f1047,plain,
    ( v1_xboole_0(sK12(sK1))
    | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f1046,f935])).

fof(f1046,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1045,f911])).

fof(f1045,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1034,f860])).

fof(f1034,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_114 ),
    inference(superposition,[],[f732,f935])).

fof(f1028,plain,
    ( spl22_11
    | ~ spl22_116 ),
    inference(avatar_contradiction_clause,[],[f1027])).

fof(f1027,plain,
    ( $false
    | ~ spl22_11
    | ~ spl22_116 ),
    inference(subsumption_resolution,[],[f1015,f376])).

fof(f1015,plain,
    ( v1_xboole_0(sK1)
    | ~ spl22_116 ),
    inference(resolution,[],[f941,f298])).

fof(f941,plain,
    ( v1_xboole_0(sK12(sK1))
    | ~ spl22_116 ),
    inference(avatar_component_clause,[],[f940])).

fof(f940,plain,
    ( spl22_116
  <=> v1_xboole_0(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_116])])).

fof(f1014,plain,
    ( spl22_128
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_117 ),
    inference(avatar_split_clause,[],[f1007,f937,f934,f910,f859,f1012])).

fof(f1007,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f1006,f938])).

fof(f1006,plain,
    ( v1_xboole_0(sK12(sK1))
    | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f1005,f935])).

fof(f1005,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f1004,f911])).

fof(f1004,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f951,f860])).

fof(f951,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_114 ),
    inference(superposition,[],[f773,f935])).

fof(f1003,plain,
    ( spl22_126
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_117 ),
    inference(avatar_split_clause,[],[f996,f937,f934,f910,f859,f1001])).

fof(f996,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f995,f938])).

fof(f995,plain,
    ( v1_xboole_0(sK12(sK1))
    | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f994,f935])).

fof(f994,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f993,f911])).

fof(f993,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f950,f860])).

fof(f950,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_114 ),
    inference(superposition,[],[f747,f935])).

fof(f992,plain,
    ( ~ spl22_125
    | spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | spl22_117 ),
    inference(avatar_split_clause,[],[f985,f937,f934,f910,f859,f990])).

fof(f985,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f984,f938])).

fof(f984,plain,
    ( v1_xboole_0(sK12(sK1))
    | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(forward_demodulation,[],[f983,f935])).

fof(f983,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_108
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f982,f911])).

fof(f982,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_99
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f949,f860])).

fof(f949,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_114 ),
    inference(superposition,[],[f732,f935])).

fof(f973,plain,
    ( ~ spl22_119
    | ~ spl22_121
    | ~ spl22_123
    | spl22_99
    | ~ spl22_100
    | ~ spl22_114 ),
    inference(avatar_split_clause,[],[f954,f934,f870,f859,f971,f965,f959])).

fof(f959,plain,
    ( spl22_119
  <=> ~ v4_tex_2(sK2(sK2(sK0,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_119])])).

fof(f965,plain,
    ( spl22_121
  <=> ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_121])])).

fof(f971,plain,
    ( spl22_123
  <=> sK1 != sK12(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_123])])).

fof(f870,plain,
    ( spl22_100
  <=> v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_100])])).

fof(f954,plain,
    ( sK1 != sK12(sK1)
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK1),sK0)
    | ~ v4_tex_2(sK2(sK2(sK0,sK1),sK1),sK0)
    | ~ spl22_99
    | ~ spl22_100
    | ~ spl22_114 ),
    inference(inner_rewriting,[],[f953])).

fof(f953,plain,
    ( sK1 != sK12(sK1)
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | ~ v4_tex_2(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | ~ spl22_99
    | ~ spl22_100
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f952,f860])).

fof(f952,plain,
    ( sK1 != sK12(sK1)
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | ~ v4_tex_2(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_100
    | ~ spl22_114 ),
    inference(subsumption_resolution,[],[f944,f871])).

fof(f871,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_100 ),
    inference(avatar_component_clause,[],[f870])).

fof(f944,plain,
    ( sK1 != sK12(sK1)
    | ~ v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | ~ v4_tex_2(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_114 ),
    inference(superposition,[],[f257,f935])).

fof(f942,plain,
    ( spl22_114
    | spl22_116
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f929,f820,f800,f729,f375,f940,f934])).

fof(f929,plain,
    ( v1_xboole_0(sK12(sK1))
    | u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) = sK12(sK1)
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f914,f376])).

fof(f914,plain,
    ( v1_xboole_0(sK12(sK1))
    | u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) = sK12(sK1)
    | v1_xboole_0(sK1)
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(resolution,[],[f850,f297])).

fof(f850,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | v1_xboole_0(X3)
        | u1_struct_0(sK2(sK2(sK0,sK1),X3)) = X3 )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f849,f730])).

fof(f849,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK0,sK1))
        | u1_struct_0(sK2(sK2(sK0,sK1),X3)) = X3 )
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f828,f801])).

fof(f828,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK0,sK1))
        | u1_struct_0(sK2(sK2(sK0,sK1),X3)) = X3 )
    | ~ spl22_94 ),
    inference(superposition,[],[f268,f821])).

fof(f928,plain,
    ( spl22_110
    | spl22_112
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f913,f820,f800,f729,f926,f920])).

fof(f913,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) = sK10(k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(resolution,[],[f850,f293])).

fof(f912,plain,
    ( spl22_108
    | ~ spl22_92
    | ~ spl22_102 ),
    inference(avatar_split_clause,[],[f905,f881,f800,f910])).

fof(f905,plain,
    ( l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_92
    | ~ spl22_102 ),
    inference(subsumption_resolution,[],[f886,f801])).

fof(f886,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102 ),
    inference(resolution,[],[f882,f273])).

fof(f904,plain,
    ( spl22_104
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_102 ),
    inference(avatar_split_clause,[],[f903,f881,f800,f783,f893])).

fof(f783,plain,
    ( spl22_88
  <=> v2_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_88])])).

fof(f903,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_102 ),
    inference(subsumption_resolution,[],[f902,f784])).

fof(f784,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_88 ),
    inference(avatar_component_clause,[],[f783])).

fof(f902,plain,
    ( ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_92
    | ~ spl22_102 ),
    inference(subsumption_resolution,[],[f885,f801])).

fof(f885,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102 ),
    inference(resolution,[],[f882,f271])).

fof(f901,plain,
    ( spl22_104
    | ~ spl22_107
    | spl22_83
    | ~ spl22_92
    | ~ spl22_102 ),
    inference(avatar_split_clause,[],[f888,f881,f800,f729,f899,f893])).

fof(f899,plain,
    ( spl22_107
  <=> ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_107])])).

fof(f888,plain,
    ( ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_102 ),
    inference(subsumption_resolution,[],[f887,f730])).

fof(f887,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_92
    | ~ spl22_102 ),
    inference(subsumption_resolution,[],[f884,f801])).

fof(f884,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102 ),
    inference(resolution,[],[f882,f303])).

fof(f883,plain,
    ( spl22_102
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f876,f820,f800,f729,f375,f881])).

fof(f876,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f875,f376])).

fof(f875,plain,
    ( v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f874,f821])).

fof(f874,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f873,f801])).

fof(f873,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f831,f730])).

fof(f831,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_94 ),
    inference(superposition,[],[f773,f821])).

fof(f872,plain,
    ( spl22_100
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f865,f820,f800,f729,f375,f870])).

fof(f865,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f864,f376])).

fof(f864,plain,
    ( v1_xboole_0(sK1)
    | v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f863,f821])).

fof(f863,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f862,f801])).

fof(f862,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f830,f730])).

fof(f830,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_94 ),
    inference(superposition,[],[f747,f821])).

fof(f861,plain,
    ( ~ spl22_99
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f854,f820,f800,f729,f375,f859])).

fof(f854,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f853,f376])).

fof(f853,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f852,f821])).

fof(f852,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f851,f801])).

fof(f851,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f829,f730])).

fof(f829,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_94 ),
    inference(superposition,[],[f732,f821])).

fof(f842,plain,
    ( ~ spl22_97
    | spl22_83
    | ~ spl22_84
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f835,f820,f770,f744,f729,f840])).

fof(f744,plain,
    ( spl22_84
  <=> v1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_84])])).

fof(f835,plain,
    ( ~ v4_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl22_83
    | ~ spl22_84
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f834,f730])).

fof(f834,plain,
    ( ~ v4_tex_2(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_84
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f833,f771])).

fof(f833,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v4_tex_2(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_84
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f832,f745])).

fof(f745,plain,
    ( v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_84 ),
    inference(avatar_component_clause,[],[f744])).

fof(f832,plain,
    ( ~ v1_pre_topc(sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v4_tex_2(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_94 ),
    inference(trivial_inequality_removal,[],[f824])).

fof(f824,plain,
    ( sK1 != sK1
    | ~ v1_pre_topc(sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v4_tex_2(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_94 ),
    inference(superposition,[],[f257,f821])).

fof(f822,plain,
    ( spl22_94
    | ~ spl22_0
    | spl22_5
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f815,f375,f368,f354,f340,f820])).

fof(f815,plain,
    ( u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f814,f355])).

fof(f814,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f813,f376])).

fof(f813,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_0
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f809,f341])).

fof(f809,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_8 ),
    inference(resolution,[],[f268,f369])).

fof(f802,plain,
    ( spl22_92
    | ~ spl22_0
    | ~ spl22_86 ),
    inference(avatar_split_clause,[],[f795,f770,f340,f800])).

fof(f795,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f776,f341])).

fof(f776,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_86 ),
    inference(resolution,[],[f771,f273])).

fof(f794,plain,
    ( spl22_88
    | ~ spl22_0
    | ~ spl22_2
    | ~ spl22_86 ),
    inference(avatar_split_clause,[],[f793,f770,f347,f340,f783])).

fof(f347,plain,
    ( spl22_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_2])])).

fof(f793,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_2
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f792,f348])).

fof(f348,plain,
    ( v2_pre_topc(sK0)
    | ~ spl22_2 ),
    inference(avatar_component_clause,[],[f347])).

fof(f792,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f775,f341])).

fof(f775,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_86 ),
    inference(resolution,[],[f771,f271])).

fof(f791,plain,
    ( spl22_88
    | ~ spl22_91
    | ~ spl22_0
    | spl22_5
    | ~ spl22_86 ),
    inference(avatar_split_clause,[],[f778,f770,f354,f340,f789,f783])).

fof(f789,plain,
    ( spl22_91
  <=> ~ v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_91])])).

fof(f778,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f777,f355])).

fof(f777,plain,
    ( v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f774,f341])).

fof(f774,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_86 ),
    inference(resolution,[],[f771,f303])).

fof(f772,plain,
    ( spl22_86
    | ~ spl22_0
    | spl22_5
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f765,f375,f368,f354,f340,f770])).

fof(f765,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f764,f355])).

fof(f764,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f763,f376])).

fof(f763,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f759,f341])).

fof(f759,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_8 ),
    inference(resolution,[],[f267,f369])).

fof(f746,plain,
    ( spl22_84
    | ~ spl22_0
    | spl22_5
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f739,f375,f368,f354,f340,f744])).

fof(f739,plain,
    ( v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f738,f355])).

fof(f738,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f737,f376])).

fof(f737,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f733,f341])).

fof(f733,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_8 ),
    inference(resolution,[],[f266,f369])).

fof(f731,plain,
    ( ~ spl22_83
    | ~ spl22_0
    | spl22_5
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f724,f375,f368,f354,f340,f729])).

fof(f724,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f723,f355])).

fof(f723,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f722,f376])).

fof(f722,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f718,f341])).

fof(f718,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_8 ),
    inference(resolution,[],[f265,f369])).

fof(f673,plain,
    ( spl22_78
    | ~ spl22_81
    | ~ spl22_48
    | spl22_51
    | ~ spl22_52 ),
    inference(avatar_split_clause,[],[f660,f522,f515,f508,f671,f665])).

fof(f665,plain,
    ( spl22_78
  <=> v1_tdlat_3(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_78])])).

fof(f671,plain,
    ( spl22_81
  <=> ~ v2_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_81])])).

fof(f508,plain,
    ( spl22_48
  <=> v7_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_48])])).

fof(f515,plain,
    ( spl22_51
  <=> ~ v2_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_51])])).

fof(f522,plain,
    ( spl22_52
  <=> l1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_52])])).

fof(f660,plain,
    ( ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ spl22_48
    | ~ spl22_51
    | ~ spl22_52 ),
    inference(subsumption_resolution,[],[f659,f523])).

fof(f523,plain,
    ( l1_pre_topc(sK17)
    | ~ spl22_52 ),
    inference(avatar_component_clause,[],[f522])).

fof(f659,plain,
    ( ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ l1_pre_topc(sK17)
    | ~ spl22_48
    | ~ spl22_51 ),
    inference(subsumption_resolution,[],[f646,f516])).

fof(f516,plain,
    ( ~ v2_struct_0(sK17)
    | ~ spl22_51 ),
    inference(avatar_component_clause,[],[f515])).

fof(f646,plain,
    ( v2_struct_0(sK17)
    | ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ l1_pre_topc(sK17)
    | ~ spl22_48 ),
    inference(resolution,[],[f305,f509])).

fof(f509,plain,
    ( v7_struct_0(sK17)
    | ~ spl22_48 ),
    inference(avatar_component_clause,[],[f508])).

fof(f305,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f250])).

fof(f250,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f249])).

fof(f249,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',cc3_tex_1)).

fof(f658,plain,
    ( spl22_76
    | ~ spl22_36
    | ~ spl22_40
    | spl22_43
    | ~ spl22_44 ),
    inference(avatar_split_clause,[],[f651,f494,f487,f480,f466,f656])).

fof(f656,plain,
    ( spl22_76
  <=> v1_tdlat_3(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_76])])).

fof(f466,plain,
    ( spl22_36
  <=> v2_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_36])])).

fof(f480,plain,
    ( spl22_40
  <=> v7_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_40])])).

fof(f487,plain,
    ( spl22_43
  <=> ~ v2_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_43])])).

fof(f494,plain,
    ( spl22_44
  <=> l1_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_44])])).

fof(f651,plain,
    ( v1_tdlat_3(sK16)
    | ~ spl22_36
    | ~ spl22_40
    | ~ spl22_43
    | ~ spl22_44 ),
    inference(subsumption_resolution,[],[f650,f495])).

fof(f495,plain,
    ( l1_pre_topc(sK16)
    | ~ spl22_44 ),
    inference(avatar_component_clause,[],[f494])).

fof(f650,plain,
    ( v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl22_36
    | ~ spl22_40
    | ~ spl22_43 ),
    inference(subsumption_resolution,[],[f649,f467])).

fof(f467,plain,
    ( v2_pre_topc(sK16)
    | ~ spl22_36 ),
    inference(avatar_component_clause,[],[f466])).

fof(f649,plain,
    ( ~ v2_pre_topc(sK16)
    | v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl22_40
    | ~ spl22_43 ),
    inference(subsumption_resolution,[],[f645,f488])).

fof(f488,plain,
    ( ~ v2_struct_0(sK16)
    | ~ spl22_43 ),
    inference(avatar_component_clause,[],[f487])).

fof(f645,plain,
    ( v2_struct_0(sK16)
    | ~ v2_pre_topc(sK16)
    | v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl22_40 ),
    inference(resolution,[],[f305,f481])).

fof(f481,plain,
    ( v7_struct_0(sK16)
    | ~ spl22_40 ),
    inference(avatar_component_clause,[],[f480])).

fof(f633,plain,
    ( spl22_74
    | ~ spl22_30 ),
    inference(avatar_split_clause,[],[f625,f445,f631])).

fof(f625,plain,
    ( sK10(k1_zfmisc_1(sK13)) = sK13
    | ~ spl22_30 ),
    inference(resolution,[],[f615,f446])).

fof(f614,plain,
    ( ~ spl22_73
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f607,f375,f368,f612])).

fof(f607,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f603,f376])).

fof(f603,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl22_8 ),
    inference(resolution,[],[f296,f369])).

fof(f587,plain,(
    spl22_70 ),
    inference(avatar_split_clause,[],[f321,f585])).

fof(f585,plain,
    ( spl22_70
  <=> l1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_70])])).

fof(f321,plain,(
    l1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f167])).

fof(f167,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc2_tex_1)).

fof(f580,plain,(
    ~ spl22_69 ),
    inference(avatar_split_clause,[],[f322,f578])).

fof(f578,plain,
    ( spl22_69
  <=> ~ v2_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_69])])).

fof(f322,plain,(
    ~ v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f167])).

fof(f573,plain,(
    ~ spl22_67 ),
    inference(avatar_split_clause,[],[f323,f571])).

fof(f571,plain,
    ( spl22_67
  <=> ~ v7_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_67])])).

fof(f323,plain,(
    ~ v7_struct_0(sK19) ),
    inference(cnf_transformation,[],[f167])).

fof(f566,plain,(
    spl22_64 ),
    inference(avatar_split_clause,[],[f324,f564])).

fof(f564,plain,
    ( spl22_64
  <=> v1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_64])])).

fof(f324,plain,(
    v1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f167])).

fof(f559,plain,(
    spl22_62 ),
    inference(avatar_split_clause,[],[f316,f557])).

fof(f557,plain,
    ( spl22_62
  <=> l1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_62])])).

fof(f316,plain,(
    l1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f186])).

fof(f186,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc4_tex_1)).

fof(f552,plain,(
    ~ spl22_61 ),
    inference(avatar_split_clause,[],[f317,f550])).

fof(f550,plain,
    ( spl22_61
  <=> ~ v2_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_61])])).

fof(f317,plain,(
    ~ v2_struct_0(sK18) ),
    inference(cnf_transformation,[],[f186])).

fof(f545,plain,(
    ~ spl22_59 ),
    inference(avatar_split_clause,[],[f318,f543])).

fof(f543,plain,
    ( spl22_59
  <=> ~ v7_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_59])])).

fof(f318,plain,(
    ~ v7_struct_0(sK18) ),
    inference(cnf_transformation,[],[f186])).

fof(f538,plain,(
    spl22_56 ),
    inference(avatar_split_clause,[],[f319,f536])).

fof(f536,plain,
    ( spl22_56
  <=> v1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_56])])).

fof(f319,plain,(
    v1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f186])).

fof(f531,plain,(
    spl22_54 ),
    inference(avatar_split_clause,[],[f320,f529])).

fof(f529,plain,
    ( spl22_54
  <=> v2_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_54])])).

fof(f320,plain,(
    v2_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f186])).

fof(f524,plain,(
    spl22_52 ),
    inference(avatar_split_clause,[],[f312,f522])).

fof(f312,plain,(
    l1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f154])).

fof(f154,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc1_tex_1)).

fof(f517,plain,(
    ~ spl22_51 ),
    inference(avatar_split_clause,[],[f313,f515])).

fof(f313,plain,(
    ~ v2_struct_0(sK17) ),
    inference(cnf_transformation,[],[f154])).

fof(f510,plain,(
    spl22_48 ),
    inference(avatar_split_clause,[],[f314,f508])).

fof(f314,plain,(
    v7_struct_0(sK17) ),
    inference(cnf_transformation,[],[f154])).

fof(f503,plain,(
    spl22_46 ),
    inference(avatar_split_clause,[],[f315,f501])).

fof(f501,plain,
    ( spl22_46
  <=> v1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_46])])).

fof(f315,plain,(
    v1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f154])).

fof(f496,plain,(
    spl22_44 ),
    inference(avatar_split_clause,[],[f307,f494])).

fof(f307,plain,(
    l1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc3_tex_1)).

fof(f489,plain,(
    ~ spl22_43 ),
    inference(avatar_split_clause,[],[f308,f487])).

fof(f308,plain,(
    ~ v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f177])).

fof(f482,plain,(
    spl22_40 ),
    inference(avatar_split_clause,[],[f309,f480])).

fof(f309,plain,(
    v7_struct_0(sK16) ),
    inference(cnf_transformation,[],[f177])).

fof(f475,plain,(
    spl22_38 ),
    inference(avatar_split_clause,[],[f310,f473])).

fof(f473,plain,
    ( spl22_38
  <=> v1_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_38])])).

fof(f310,plain,(
    v1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f177])).

fof(f468,plain,(
    spl22_36 ),
    inference(avatar_split_clause,[],[f311,f466])).

fof(f311,plain,(
    v2_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f177])).

fof(f461,plain,(
    spl22_34 ),
    inference(avatar_split_clause,[],[f302,f459])).

fof(f459,plain,
    ( spl22_34
  <=> l1_pre_topc(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_34])])).

fof(f302,plain,(
    l1_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',existence_l1_pre_topc)).

fof(f454,plain,(
    ~ spl22_33 ),
    inference(avatar_split_clause,[],[f301,f452])).

fof(f452,plain,
    ( spl22_33
  <=> ~ v1_xboole_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_33])])).

fof(f301,plain,(
    ~ v1_xboole_0(sK14) ),
    inference(cnf_transformation,[],[f170])).

fof(f170,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc2_xboole_0)).

fof(f447,plain,(
    spl22_30 ),
    inference(avatar_split_clause,[],[f300,f445])).

fof(f300,plain,(
    v1_xboole_0(sK13) ),
    inference(cnf_transformation,[],[f157])).

fof(f157,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc1_xboole_0)).

fof(f440,plain,(
    spl22_28 ),
    inference(avatar_split_clause,[],[f279,f438])).

fof(f438,plain,
    ( spl22_28
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_28])])).

fof(f279,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f162])).

fof(f162,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc2_pre_topc)).

fof(f433,plain,(
    ~ spl22_27 ),
    inference(avatar_split_clause,[],[f280,f431])).

fof(f431,plain,
    ( spl22_27
  <=> ~ v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_27])])).

fof(f280,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f162])).

fof(f426,plain,(
    spl22_24 ),
    inference(avatar_split_clause,[],[f281,f424])).

fof(f424,plain,
    ( spl22_24
  <=> v1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_24])])).

fof(f281,plain,(
    v1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f162])).

fof(f419,plain,(
    spl22_22 ),
    inference(avatar_split_clause,[],[f282,f417])).

fof(f417,plain,
    ( spl22_22
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_22])])).

fof(f282,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f162])).

fof(f412,plain,(
    spl22_20 ),
    inference(avatar_split_clause,[],[f277,f410])).

fof(f410,plain,
    ( spl22_20
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_20])])).

fof(f277,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc1_pre_topc)).

fof(f405,plain,(
    spl22_18 ),
    inference(avatar_split_clause,[],[f278,f403])).

fof(f403,plain,
    ( spl22_18
  <=> v1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_18])])).

fof(f278,plain,(
    v1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f149])).

fof(f398,plain,(
    spl22_16 ),
    inference(avatar_split_clause,[],[f274,f396])).

fof(f396,plain,
    ( spl22_16
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_16])])).

fof(f274,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f139])).

fof(f139,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t53_tex_2.p',rc11_pre_topc)).

fof(f391,plain,(
    spl22_14 ),
    inference(avatar_split_clause,[],[f275,f389])).

fof(f389,plain,
    ( spl22_14
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_14])])).

fof(f275,plain,(
    v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f139])).

fof(f384,plain,(
    spl22_12 ),
    inference(avatar_split_clause,[],[f276,f382])).

fof(f382,plain,
    ( spl22_12
  <=> v1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_12])])).

fof(f276,plain,(
    v1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f139])).

fof(f377,plain,(
    ~ spl22_11 ),
    inference(avatar_split_clause,[],[f258,f375])).

fof(f258,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f224])).

fof(f370,plain,(
    spl22_8 ),
    inference(avatar_split_clause,[],[f259,f368])).

fof(f259,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f224])).

fof(f363,plain,(
    spl22_6 ),
    inference(avatar_split_clause,[],[f260,f361])).

fof(f260,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f224])).

fof(f356,plain,(
    ~ spl22_5 ),
    inference(avatar_split_clause,[],[f261,f354])).

fof(f261,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f224])).

fof(f349,plain,(
    spl22_2 ),
    inference(avatar_split_clause,[],[f262,f347])).

fof(f262,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f224])).

fof(f342,plain,(
    spl22_0 ),
    inference(avatar_split_clause,[],[f263,f340])).

fof(f263,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f224])).
%------------------------------------------------------------------------------
