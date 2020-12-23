%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t61_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:46 EDT 2019

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  854 (3828 expanded)
%              Number of leaves         :  184 (1390 expanded)
%              Depth                    :   20
%              Number of atoms          : 3138 (10497 expanded)
%              Number of equality atoms :  130 (1588 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7654,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f105,f112,f125,f132,f139,f140,f141,f154,f180,f195,f237,f247,f268,f270,f283,f291,f311,f340,f370,f421,f471,f505,f530,f546,f553,f581,f585,f709,f777,f811,f1007,f1103,f1121,f1124,f1145,f1172,f1177,f1181,f1218,f1232,f1236,f1241,f1257,f1260,f1378,f1385,f1532,f1541,f1542,f1543,f1544,f1621,f1656,f1675,f1718,f1725,f1828,f1935,f1988,f2015,f2045,f2055,f2059,f2114,f2118,f2122,f2126,f2127,f2131,f2135,f2148,f2152,f2179,f2182,f2209,f2215,f2230,f2241,f2254,f2256,f2263,f2319,f2424,f2442,f2552,f2555,f2577,f2623,f2791,f2795,f2879,f2997,f3058,f3302,f3666,f3809,f4001,f4071,f4176,f4347,f4363,f4424,f4466,f4561,f4729,f4736,f4877,f4948,f4949,f5043,f5105,f5350,f5556,f5563,f5841,f6100,f6198,f6346,f6413,f6420,f6923,f6925,f6942,f7002,f7450,f7528,f7544,f7551,f7556,f7559,f7653])).

fof(f7653,plain,
    ( ~ spl5_2
    | spl5_7
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_268 ),
    inference(avatar_contradiction_clause,[],[f7652])).

fof(f7652,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_268 ),
    inference(subsumption_resolution,[],[f7651,f115])).

fof(f115,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_7
  <=> ~ v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f7651,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_268 ),
    inference(subsumption_resolution,[],[f7650,f131])).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f7650,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_268 ),
    inference(resolution,[],[f7550,f227])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f221,f214])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f213,f104])).

fof(f104,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl5_14 ),
    inference(superposition,[],[f87,f153])).

fof(f153,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl5_14
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',d6_pre_topc)).

fof(f221,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0) = k4_xboole_0(u1_struct_0(sK0),X0)
    | ~ spl5_18 ),
    inference(resolution,[],[f179,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',redefinition_k7_subset_1)).

fof(f179,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl5_18
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f7550,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_268 ),
    inference(avatar_component_clause,[],[f7549])).

fof(f7549,plain,
    ( spl5_268
  <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_268])])).

fof(f7559,plain,
    ( ~ spl5_2
    | spl5_9
    | ~ spl5_10
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118
    | ~ spl5_268 ),
    inference(avatar_contradiction_clause,[],[f7558])).

fof(f7558,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118
    | ~ spl5_268 ),
    inference(subsumption_resolution,[],[f7550,f7557])).

fof(f7557,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f7552,f131])).

fof(f7552,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(resolution,[],[f121,f7003])).

fof(f7003,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) )
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(resolution,[],[f2165,f454])).

fof(f454,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f453,f221])).

fof(f453,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f452,f179])).

fof(f452,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f447,f104])).

fof(f447,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_18 ),
    inference(superposition,[],[f204,f221])).

fof(f204,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k7_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),X2,X3),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f75,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',dt_k7_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',d5_pre_topc)).

fof(f2165,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_xboole_0(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2164,f1827])).

fof(f1827,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f1826,plain,
    ( spl5_118
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f2164,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_xboole_0(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2163,f221])).

fof(f2163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2162,f1827])).

fof(f2162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114 ),
    inference(forward_demodulation,[],[f2161,f1717])).

fof(f1717,plain,
    ( u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f1716])).

fof(f1716,plain,
    ( spl5_114
  <=> u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f2161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(subsumption_resolution,[],[f2154,f264])).

fof(f264,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl5_32
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f2154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(resolution,[],[f1457,f87])).

fof(f1457,plain,
    ( ! [X10] :
        ( v3_pre_topc(X10,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r2_hidden(X10,u1_pre_topc(sK0)) )
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(subsumption_resolution,[],[f1417,f264])).

fof(f1417,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,u1_pre_topc(sK0))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v3_pre_topc(X10,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_102 ),
    inference(superposition,[],[f320,f1377])).

fof(f1377,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f1376])).

fof(f1376,plain,
    ( spl5_102
  <=> u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f320,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,u1_pre_topc(X3))
      | ~ l1_pre_topc(X3)
      | v3_pre_topc(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,u1_pre_topc(X3))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ r2_hidden(X2,u1_pre_topc(X3))
      | v3_pre_topc(X2,X3) ) ),
    inference(resolution,[],[f162,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f162,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,u1_pre_topc(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f78,f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',dt_u1_pre_topc)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',t4_subset)).

fof(f121,plain,
    ( ~ v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_9
  <=> ~ v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f7556,plain,
    ( ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_18
    | spl5_269 ),
    inference(avatar_contradiction_clause,[],[f7555])).

fof(f7555,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_269 ),
    inference(subsumption_resolution,[],[f7554,f118])).

fof(f118,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_6
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f7554,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_269 ),
    inference(subsumption_resolution,[],[f7553,f131])).

fof(f7553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_269 ),
    inference(resolution,[],[f7547,f226])).

fof(f226,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f221,f218])).

fof(f218,plain,
    ( ! [X0] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f216,f104])).

fof(f216,plain,
    ( ! [X0] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_14 ),
    inference(superposition,[],[f88,f153])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f7547,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_269 ),
    inference(avatar_component_clause,[],[f7546])).

fof(f7546,plain,
    ( spl5_269
  <=> ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_269])])).

fof(f7551,plain,
    ( spl5_268
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f7533,f1826,f1716,f1376,f263,f178,f130,f123,f103,f7549])).

fof(f123,plain,
    ( spl5_8
  <=> v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f7533,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f7529,f131])).

fof(f7529,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(resolution,[],[f7458,f124])).

fof(f124,plain,
    ( v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f7458,plain,
    ( ! [X1] :
        ( ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X1),sK0) )
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(resolution,[],[f3293,f457])).

fof(f457,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(u1_struct_0(sK0),X1),u1_pre_topc(sK0))
        | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X1),sK0) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f456,f221])).

fof(f456,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(u1_struct_0(sK0),X1),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1),sK0) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f455,f179])).

fof(f455,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(u1_struct_0(sK0),X1),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f448,f104])).

fof(f448,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(u1_struct_0(sK0),X1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_18 ),
    inference(superposition,[],[f197,f221])).

fof(f197,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(k7_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X1),X2,X3),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f74,f83])).

fof(f3293,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f3292,f1827])).

fof(f3292,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f3291,f221])).

fof(f3291,plain,
    ( ! [X0] :
        ( r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f3290,f1827])).

fof(f3290,plain,
    ( ! [X0] :
        ( r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f3289,f1717])).

fof(f3289,plain,
    ( ! [X0] :
        ( r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f3288,f459])).

fof(f459,plain,
    ( ! [X6] : m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X6),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f451,f179])).

fof(f451,plain,
    ( ! [X6] :
        ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X6),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_18 ),
    inference(superposition,[],[f83,f221])).

fof(f3288,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_18
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f3287,f221])).

fof(f3287,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f3286,f1827])).

fof(f3286,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_114
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f3285,f1717])).

fof(f3285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f3280,f264])).

fof(f3280,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(resolution,[],[f1870,f88])).

fof(f1870,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,u1_pre_topc(sK0)) )
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f1869,f1377])).

fof(f1869,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f1842,f264])).

fof(f1842,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_118 ),
    inference(superposition,[],[f75,f1827])).

fof(f7544,plain,
    ( ~ spl5_263
    | spl5_266
    | ~ spl5_172
    | ~ spl5_174
    | ~ spl5_188
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f7424,f4727,f2877,f2544,f2440,f7542,f7520])).

fof(f7520,plain,
    ( spl5_263
  <=> ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_263])])).

fof(f7542,plain,
    ( spl5_266
  <=> m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_266])])).

fof(f2440,plain,
    ( spl5_172
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f2544,plain,
    ( spl5_174
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f2877,plain,
    ( spl5_188
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f4727,plain,
    ( spl5_224
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).

fof(f7424,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172
    | ~ spl5_174
    | ~ spl5_188
    | ~ spl5_224 ),
    inference(subsumption_resolution,[],[f7396,f4728])).

fof(f4728,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_224 ),
    inference(avatar_component_clause,[],[f4727])).

fof(f7396,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172
    | ~ spl5_174
    | ~ spl5_188 ),
    inference(backward_demodulation,[],[f7393,f2473])).

fof(f2473,plain,
    ( ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172 ),
    inference(forward_demodulation,[],[f2466,f2441])).

fof(f2441,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172 ),
    inference(avatar_component_clause,[],[f2440])).

fof(f2466,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172 ),
    inference(superposition,[],[f327,f2441])).

fof(f327,plain,(
    ! [X1] :
      ( m1_subset_1(k2_struct_0(X1),u1_pre_topc(X1))
      | ~ v3_pre_topc(k2_struct_0(X1),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f209,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',t1_subset)).

fof(f209,plain,(
    ! [X0] :
      ( r2_hidden(k2_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(subsumption_resolution,[],[f203,f91])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',dt_l1_pre_topc)).

fof(f203,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(k2_struct_0(X0),u1_pre_topc(X0))
      | ~ v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f75,f86])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',dt_k2_struct_0)).

fof(f7393,plain,
    ( u1_pre_topc(sK4) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_174
    | ~ spl5_188 ),
    inference(subsumption_resolution,[],[f7392,f2545])).

fof(f2545,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl5_174 ),
    inference(avatar_component_clause,[],[f2544])).

fof(f7392,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | u1_pre_topc(sK4) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_188 ),
    inference(equality_resolution,[],[f2887])).

fof(f2887,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X2 )
    | ~ spl5_188 ),
    inference(superposition,[],[f68,f2878])).

fof(f2878,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_188 ),
    inference(avatar_component_clause,[],[f2877])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',free_g1_pre_topc)).

fof(f7528,plain,
    ( ~ spl5_263
    | spl5_264
    | ~ spl5_172
    | ~ spl5_174
    | ~ spl5_188
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f7423,f4727,f2877,f2544,f2440,f7526,f7520])).

fof(f7526,plain,
    ( spl5_264
  <=> r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_264])])).

fof(f7423,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172
    | ~ spl5_174
    | ~ spl5_188
    | ~ spl5_224 ),
    inference(subsumption_resolution,[],[f7395,f4728])).

fof(f7395,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172
    | ~ spl5_174
    | ~ spl5_188 ),
    inference(backward_demodulation,[],[f7393,f2471])).

fof(f2471,plain,
    ( ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172 ),
    inference(forward_demodulation,[],[f2462,f2441])).

fof(f2462,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172 ),
    inference(superposition,[],[f209,f2441])).

fof(f7450,plain,
    ( spl5_260
    | ~ spl5_174
    | ~ spl5_188 ),
    inference(avatar_split_clause,[],[f7397,f2877,f2544,f7448])).

fof(f7448,plain,
    ( spl5_260
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_260])])).

fof(f7397,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ spl5_174
    | ~ spl5_188 ),
    inference(backward_demodulation,[],[f7393,f2878])).

fof(f7002,plain,
    ( ~ spl5_253
    | ~ spl5_257
    | spl5_258
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f2459,f2440,f7000,f6997,f6915])).

fof(f6915,plain,
    ( spl5_253
  <=> ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_253])])).

fof(f6997,plain,
    ( spl5_257
  <=> ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_257])])).

fof(f7000,plain,
    ( spl5_258
  <=> ! [X2] : ~ r2_hidden(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_258])])).

fof(f2459,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_172 ),
    inference(superposition,[],[f158,f2441])).

fof(f158,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_struct_0(X3))
      | ~ v1_xboole_0(u1_struct_0(X3))
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f77,f86])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',t5_subset)).

fof(f6942,plain,
    ( ~ spl5_224
    | spl5_253 ),
    inference(avatar_contradiction_clause,[],[f6941])).

fof(f6941,plain,
    ( $false
    | ~ spl5_224
    | ~ spl5_253 ),
    inference(subsumption_resolution,[],[f6940,f4728])).

fof(f6940,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_253 ),
    inference(resolution,[],[f6916,f91])).

fof(f6916,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_253 ),
    inference(avatar_component_clause,[],[f6915])).

fof(f6925,plain,(
    spl5_255 ),
    inference(avatar_contradiction_clause,[],[f6924])).

fof(f6924,plain,
    ( $false
    | ~ spl5_255 ),
    inference(subsumption_resolution,[],[f6919,f3259])).

fof(f3259,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f3258,f147])).

fof(f147,plain,(
    ! [X0] : l1_pre_topc(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))) ),
    inference(resolution,[],[f70,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',existence_m1_subset_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',dt_g1_pre_topc)).

fof(f3258,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ l1_pre_topc(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))) ) ),
    inference(resolution,[],[f3129,f91])).

fof(f3129,plain,(
    ! [X0] :
      ( ~ l1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))))
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f3125,f721])).

fof(f721,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))))))
      | ~ l1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))) ) ),
    inference(superposition,[],[f86,f286])).

fof(f286,plain,(
    ! [X0] : u1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))) = k2_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))) ),
    inference(resolution,[],[f147,f142])).

fof(f142,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f89,f91])).

fof(f89,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',d3_struct_0)).

fof(f3125,plain,(
    ! [X0] : u1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))) = X0 ),
    inference(subsumption_resolution,[],[f3124,f81])).

fof(f3124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_zfmisc_1(X0))),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | u1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))) = X0 ) ),
    inference(equality_resolution,[],[f879])).

fof(f879,plain,(
    ! [X12,X10,X11] :
      ( g1_pre_topc(X11,X12) != g1_pre_topc(X10,sK2(k1_zfmisc_1(k1_zfmisc_1(X10))))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11)))
      | u1_struct_0(g1_pre_topc(X10,sK2(k1_zfmisc_1(k1_zfmisc_1(X10))))) = X11 ) ),
    inference(superposition,[],[f67,f285])).

fof(f285,plain,(
    ! [X0] : g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))),u1_pre_topc(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ),
    inference(subsumption_resolution,[],[f284,f147])).

fof(f284,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))))
      | g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))),u1_pre_topc(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ) ),
    inference(resolution,[],[f146,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',abstractness_v1_pre_topc)).

fof(f146,plain,(
    ! [X0] : v1_pre_topc(g1_pre_topc(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0))))) ),
    inference(resolution,[],[f69,f81])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6919,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_255 ),
    inference(avatar_component_clause,[],[f6918])).

fof(f6918,plain,
    ( spl5_255
  <=> ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_255])])).

fof(f6923,plain,
    ( ~ spl5_253
    | spl5_254
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f2456,f2440,f6921,f6915])).

fof(f6921,plain,
    ( spl5_254
  <=> m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_254])])).

fof(f2456,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_172 ),
    inference(superposition,[],[f86,f2441])).

fof(f6420,plain,
    ( ~ spl5_175
    | ~ spl5_183
    | spl5_250
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f2394,f110,f6418,f2786,f2547])).

fof(f2547,plain,
    ( spl5_175
  <=> ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f2786,plain,
    ( spl5_183
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).

fof(f6418,plain,
    ( spl5_250
  <=> ! [X18] : v1_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_250])])).

fof(f110,plain,
    ( spl5_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2394,plain,
    ( ! [X18] :
        ( v1_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X18))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f796,f376])).

fof(f376,plain,
    ( ! [X1] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),u1_pre_topc(sK4),X1) = k4_xboole_0(u1_pre_topc(sK4),X1)
    | ~ spl5_4 ),
    inference(resolution,[],[f187,f111])).

fof(f111,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),u1_pre_topc(X0),X1) = k4_xboole_0(u1_pre_topc(X0),X1) ) ),
    inference(resolution,[],[f82,f76])).

fof(f796,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k7_subset_1(X0,X1,X2))
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f341,f81])).

fof(f341,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k7_subset_1(X1,X0,X2))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(k7_subset_1(X1,X0,X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f186,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',t2_subset)).

fof(f186,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(X12,k7_subset_1(X11,X10,X13))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | ~ v1_xboole_0(X11) ) ),
    inference(resolution,[],[f83,f77])).

fof(f6413,plain,
    ( spl5_170
    | spl5_248
    | ~ spl5_4
    | ~ spl5_54
    | ~ spl5_150 ),
    inference(avatar_split_clause,[],[f2340,f2177,f544,f110,f6411,f2422])).

fof(f2422,plain,
    ( spl5_170
  <=> v1_xboole_0(u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).

fof(f6411,plain,
    ( spl5_248
  <=> ! [X0] :
        ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK4),X0),sK4)
        | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK4),X0),u1_pre_topc(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_248])])).

fof(f544,plain,
    ( spl5_54
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f2177,plain,
    ( spl5_150
  <=> m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f2340,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK4),X0),sK4)
        | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
        | v1_xboole_0(u1_pre_topc(sK4)) )
    | ~ spl5_4
    | ~ spl5_54
    | ~ spl5_150 ),
    inference(forward_demodulation,[],[f2339,f691])).

fof(f691,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK4),u1_struct_0(sK4),X1) = k4_xboole_0(u1_struct_0(sK4),X1)
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f684,f545])).

fof(f545,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f544])).

fof(f684,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK4),k2_struct_0(sK4),X1) = k4_xboole_0(k2_struct_0(sK4),X1)
    | ~ spl5_4 ),
    inference(resolution,[],[f361,f111])).

fof(f361,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k4_xboole_0(k2_struct_0(X0),X1) ) ),
    inference(resolution,[],[f188,f91])).

fof(f188,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3) = k4_xboole_0(k2_struct_0(X2),X3) ) ),
    inference(resolution,[],[f82,f86])).

fof(f2339,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK4),u1_struct_0(sK4),X0),sK4)
        | v1_xboole_0(u1_pre_topc(sK4)) )
    | ~ spl5_4
    | ~ spl5_54
    | ~ spl5_150 ),
    inference(subsumption_resolution,[],[f2338,f111])).

fof(f2338,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK4),u1_struct_0(sK4),X0),sK4)
        | v1_xboole_0(u1_pre_topc(sK4))
        | ~ l1_pre_topc(sK4) )
    | ~ spl5_4
    | ~ spl5_54
    | ~ spl5_150 ),
    inference(subsumption_resolution,[],[f2329,f2178])).

fof(f2178,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_150 ),
    inference(avatar_component_clause,[],[f2177])).

fof(f2329,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK4),u1_struct_0(sK4),X0),sK4)
        | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
        | v1_xboole_0(u1_pre_topc(sK4))
        | ~ l1_pre_topc(sK4) )
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(superposition,[],[f403,f691])).

fof(f403,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f197,f79])).

fof(f6346,plain,
    ( ~ spl5_247
    | ~ spl5_32
    | ~ spl5_102
    | spl5_243 ),
    inference(avatar_split_clause,[],[f6297,f6089,f1376,f263,f6344])).

fof(f6344,plain,
    ( spl5_247
  <=> ~ r2_hidden(sK2(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_247])])).

fof(f6089,plain,
    ( spl5_243
  <=> ~ v3_pre_topc(sK2(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_243])])).

fof(f6297,plain,
    ( ~ r2_hidden(sK2(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))),u1_pre_topc(sK0))
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_243 ),
    inference(resolution,[],[f6090,f1457])).

fof(f6090,plain,
    ( ~ v3_pre_topc(sK2(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_243 ),
    inference(avatar_component_clause,[],[f6089])).

fof(f6198,plain,
    ( ~ spl5_40
    | spl5_245 ),
    inference(avatar_contradiction_clause,[],[f6197])).

fof(f6197,plain,
    ( $false
    | ~ spl5_40
    | ~ spl5_245 ),
    inference(subsumption_resolution,[],[f6196,f310])).

fof(f310,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl5_40
  <=> v1_xboole_0(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f6196,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl5_245 ),
    inference(resolution,[],[f6096,f631])).

fof(f631,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f287,f81])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK2(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK2(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f160,f79])).

fof(f160,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK2(k1_zfmisc_1(X6)))
      | ~ v1_xboole_0(X6) ) ),
    inference(resolution,[],[f77,f81])).

fof(f6096,plain,
    ( ~ v1_xboole_0(sK2(k1_zfmisc_1(u1_pre_topc(sK0))))
    | ~ spl5_245 ),
    inference(avatar_component_clause,[],[f6095])).

fof(f6095,plain,
    ( spl5_245
  <=> ~ v1_xboole_0(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_245])])).

fof(f6100,plain,
    ( spl5_242
    | spl5_244
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f6012,f1376,f263,f6098,f6092])).

fof(f6092,plain,
    ( spl5_242
  <=> v3_pre_topc(sK2(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_242])])).

fof(f6098,plain,
    ( spl5_244
  <=> v1_xboole_0(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_244])])).

fof(f6012,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(u1_pre_topc(sK0))))
    | v3_pre_topc(sK2(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f6011,f1377])).

fof(f6011,plain,
    ( v3_pre_topc(sK2(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK2(k1_zfmisc_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(subsumption_resolution,[],[f6005,f264])).

fof(f6005,plain,
    ( v3_pre_topc(sK2(sK2(k1_zfmisc_1(u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK2(k1_zfmisc_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl5_102 ),
    inference(superposition,[],[f2415,f1377])).

fof(f2415,plain,(
    ! [X12] :
      ( v3_pre_topc(sK2(sK2(k1_zfmisc_1(u1_pre_topc(X12)))),X12)
      | ~ l1_pre_topc(X12)
      | v1_xboole_0(sK2(k1_zfmisc_1(u1_pre_topc(X12)))) ) ),
    inference(subsumption_resolution,[],[f2408,f631])).

fof(f2408,plain,(
    ! [X12] :
      ( v3_pre_topc(sK2(sK2(k1_zfmisc_1(u1_pre_topc(X12)))),X12)
      | v1_xboole_0(u1_pre_topc(X12))
      | ~ l1_pre_topc(X12)
      | v1_xboole_0(sK2(k1_zfmisc_1(u1_pre_topc(X12)))) ) ),
    inference(resolution,[],[f605,f644])).

fof(f644,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK2(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK2(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f296,f81])).

fof(f296,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2(k1_zfmisc_1(X1)))
      | v1_xboole_0(sK2(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f165,f79])).

fof(f165,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK2(k1_zfmisc_1(X6)))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f78,f81])).

fof(f605,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f320,f79])).

fof(f5841,plain,
    ( ~ spl5_239
    | spl5_240
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f1977,f1933,f103,f5839,f5833])).

fof(f5833,plain,
    ( spl5_239
  <=> ~ v3_pre_topc(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_239])])).

fof(f5839,plain,
    ( spl5_240
  <=> r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_240])])).

fof(f1933,plain,
    ( spl5_120
  <=> m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f1977,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f1970,f104])).

fof(f1970,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl5_120 ),
    inference(resolution,[],[f1934,f75])).

fof(f1934,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f1933])).

fof(f5563,plain,
    ( ~ spl5_183
    | spl5_236
    | ~ spl5_4
    | ~ spl5_180 ),
    inference(avatar_split_clause,[],[f2776,f2621,f110,f5561,f2786])).

fof(f5561,plain,
    ( spl5_236
  <=> ! [X16,X15,X14] : ~ r2_hidden(X16,k4_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X14),X15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_236])])).

fof(f2621,plain,
    ( spl5_180
  <=> ! [X6] : m1_subset_1(k4_xboole_0(u1_pre_topc(sK4),X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f2776,plain,
    ( ! [X14,X15,X16] :
        ( ~ r2_hidden(X16,k4_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X14),X15))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl5_4
    | ~ spl5_180 ),
    inference(subsumption_resolution,[],[f2765,f2622])).

fof(f2622,plain,
    ( ! [X6] : m1_subset_1(k4_xboole_0(u1_pre_topc(sK4),X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl5_180 ),
    inference(avatar_component_clause,[],[f2621])).

fof(f2765,plain,
    ( ! [X14,X15,X16] :
        ( ~ r2_hidden(X16,k4_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X14),X15))
        | ~ m1_subset_1(k4_xboole_0(u1_pre_topc(sK4),X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f186,f959])).

fof(f959,plain,
    ( ! [X2,X3] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),k4_xboole_0(u1_pre_topc(sK4),X2),X3) = k4_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X2),X3)
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f952,f376])).

fof(f952,plain,
    ( ! [X2,X3] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),u1_pre_topc(sK4),X2),X3) = k4_xboole_0(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),u1_pre_topc(sK4),X2),X3)
    | ~ spl5_4 ),
    inference(resolution,[],[f394,f111])).

fof(f394,plain,(
    ! [X6,X8,X7] :
      ( ~ l1_pre_topc(X6)
      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X6)),k7_subset_1(k1_zfmisc_1(u1_struct_0(X6)),u1_pre_topc(X6),X7),X8) = k4_xboole_0(k7_subset_1(k1_zfmisc_1(u1_struct_0(X6)),u1_pre_topc(X6),X7),X8) ) ),
    inference(resolution,[],[f189,f76])).

fof(f189,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | k7_subset_1(X4,k7_subset_1(X4,X5,X6),X7) = k4_xboole_0(k7_subset_1(X4,X5,X6),X7) ) ),
    inference(resolution,[],[f82,f83])).

fof(f5556,plain,
    ( ~ spl5_183
    | spl5_234
    | ~ spl5_4
    | ~ spl5_180 ),
    inference(avatar_split_clause,[],[f2779,f2621,f110,f5554,f2786])).

fof(f5554,plain,
    ( spl5_234
  <=> ! [X23,X24] : v1_xboole_0(k4_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X23),X24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_234])])).

fof(f2779,plain,
    ( ! [X24,X23] :
        ( v1_xboole_0(k4_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X23),X24))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl5_4
    | ~ spl5_180 ),
    inference(subsumption_resolution,[],[f2768,f2622])).

fof(f2768,plain,
    ( ! [X24,X23] :
        ( v1_xboole_0(k4_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X23),X24))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(k4_xboole_0(u1_pre_topc(sK4),X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f796,f959])).

fof(f5350,plain,
    ( ~ spl5_183
    | spl5_184
    | ~ spl5_180 ),
    inference(avatar_split_clause,[],[f2643,f2621,f2789,f2786])).

fof(f2789,plain,
    ( spl5_184
  <=> ! [X5,X4] : ~ r2_hidden(X5,k4_xboole_0(u1_pre_topc(sK4),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f2643,plain,
    ( ! [X21,X20] :
        ( ~ r2_hidden(X20,k4_xboole_0(u1_pre_topc(sK4),X21))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl5_180 ),
    inference(resolution,[],[f2622,f77])).

fof(f5105,plain,
    ( ~ spl5_183
    | spl5_232
    | ~ spl5_174 ),
    inference(avatar_split_clause,[],[f2566,f2544,f5103,f2786])).

fof(f5103,plain,
    ( spl5_232
  <=> ! [X11] : ~ r2_hidden(X11,u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).

fof(f2566,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,u1_pre_topc(sK4))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl5_174 ),
    inference(resolution,[],[f2545,f77])).

fof(f5043,plain,
    ( ~ spl5_167
    | spl5_170
    | spl5_163 ),
    inference(avatar_split_clause,[],[f2255,f2246,f2422,f2258])).

fof(f2258,plain,
    ( spl5_167
  <=> ~ m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f2246,plain,
    ( spl5_163
  <=> ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f2255,plain,
    ( v1_xboole_0(u1_pre_topc(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_163 ),
    inference(resolution,[],[f2247,f79])).

fof(f2247,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_163 ),
    inference(avatar_component_clause,[],[f2246])).

fof(f4949,plain,
    ( ~ spl5_159
    | spl5_160
    | ~ spl5_150 ),
    inference(avatar_split_clause,[],[f2195,f2177,f2239,f2236])).

fof(f2236,plain,
    ( spl5_159
  <=> ~ v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f2239,plain,
    ( spl5_160
  <=> ! [X2] : ~ r2_hidden(X2,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f2195,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,u1_struct_0(sK4))
        | ~ v1_xboole_0(u1_struct_0(sK4)) )
    | ~ spl5_150 ),
    inference(resolution,[],[f2178,f77])).

fof(f4948,plain,
    ( spl5_40
    | spl5_230
    | ~ spl5_2
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f2061,f1986,f1113,f579,f573,f528,f263,f103,f4946,f309])).

fof(f4946,plain,
    ( spl5_230
  <=> ! [X1,X0] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_230])])).

fof(f528,plain,
    ( spl5_52
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f573,plain,
    ( spl5_58
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f579,plain,
    ( spl5_60
  <=> ! [X10] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X10) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1113,plain,
    ( spl5_76
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1986,plain,
    ( spl5_122
  <=> ! [X6] : m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X6),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f2061,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2060,f1571])).

fof(f1571,plain,
    ( ! [X19,X20] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X19),X20) = k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X19),X20)
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f950])).

fof(f950,plain,
    ( ! [X19,X20] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X19),X20) = k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X19),X20)
    | ~ spl5_32
    | ~ spl5_58
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f949,f580])).

fof(f580,plain,
    ( ! [X10] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X10) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X10)
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f579])).

fof(f949,plain,
    ( ! [X19,X20] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X19),X20) = k4_xboole_0(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X19),X20)
    | ~ spl5_32
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f946,f574])).

fof(f574,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f573])).

fof(f946,plain,
    ( ! [X19,X20] :
        ( k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X19),X20) = k4_xboole_0(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X19),X20)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32 ),
    inference(resolution,[],[f399,f264])).

fof(f399,plain,(
    ! [X24,X23,X22] :
      ( ~ l1_pre_topc(X22)
      | k7_subset_1(u1_struct_0(X22),k7_subset_1(u1_struct_0(X22),sK3(X22),X23),X24) = k4_xboole_0(k7_subset_1(u1_struct_0(X22),sK3(X22),X23),X24)
      | ~ v2_pre_topc(X22) ) ),
    inference(resolution,[],[f189,f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',rc6_pre_topc)).

fof(f1548,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1547,f1114])).

fof(f1114,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f1547,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_52 ),
    inference(equality_resolution,[],[f537])).

fof(f537,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X4 )
    | ~ spl5_52 ),
    inference(superposition,[],[f67,f529])).

fof(f529,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f528])).

fof(f2060,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),sK0)
        | v1_xboole_0(u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f2025,f104])).

fof(f2025,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),sK0)
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f2016,f1987])).

fof(f1987,plain,
    ( ! [X6] : m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X6),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f1986])).

fof(f2016,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),X1),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(superposition,[],[f403,f1571])).

fof(f4877,plain,
    ( spl5_228
    | spl5_40
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f2090,f1826,f1376,f1113,f528,f263,f137,f309,f4875])).

fof(f4875,plain,
    ( spl5_228
  <=> ! [X1,X0,X2] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_228])])).

fof(f137,plain,
    ( spl5_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2090,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(u1_pre_topc(sK0))
        | v3_pre_topc(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0)) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2089,f1377])).

fof(f2089,plain,
    ( ! [X2,X0,X1] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2088,f1556])).

fof(f1556,plain,
    ( ! [X4,X2,X3] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(sK1,X2),X3),X4) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X2),X3),X4)
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f437])).

fof(f437,plain,
    ( ! [X4,X2,X3] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(k4_xboole_0(sK1,X2),X3),X4) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X2),X3),X4)
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f433,f401])).

fof(f401,plain,
    ( ! [X17,X18] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(sK1,X17),X18) = k4_xboole_0(k4_xboole_0(sK1,X17),X18)
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f397,f190])).

fof(f190,plain,
    ( ! [X8] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1,X8) = k4_xboole_0(sK1,X8)
    | ~ spl5_12 ),
    inference(resolution,[],[f82,f138])).

fof(f138,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f397,plain,
    ( ! [X17,X18] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1,X17),X18) = k4_xboole_0(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1,X17),X18)
    | ~ spl5_12 ),
    inference(resolution,[],[f189,f138])).

fof(f433,plain,
    ( ! [X4,X2,X3] : k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(sK1,X2),X3),X4) = k4_xboole_0(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(sK1,X2),X3),X4)
    | ~ spl5_12 ),
    inference(resolution,[],[f249,f189])).

fof(f249,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f248,f138])).

fof(f248,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_12 ),
    inference(superposition,[],[f83,f190])).

fof(f2088,plain,
    ( ! [X2,X0,X1] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2087,f1827])).

fof(f2087,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f2086,f1377])).

fof(f2086,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f1286,f264])).

fof(f1286,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1277,f518])).

fof(f518,plain,
    ( ! [X10,X11] : m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X10),X11),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f510,f249])).

fof(f510,plain,
    ( ! [X10,X11] :
        ( m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X10),X11),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(k4_xboole_0(sK1,X10),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_12 ),
    inference(superposition,[],[f83,f401])).

fof(f1277,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X0),X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_12 ),
    inference(superposition,[],[f403,f437])).

fof(f4736,plain,
    ( spl5_226
    | ~ spl5_174 ),
    inference(avatar_split_clause,[],[f2561,f2544,f4734])).

fof(f4734,plain,
    ( spl5_226
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_226])])).

fof(f2561,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_174 ),
    inference(resolution,[],[f2545,f69])).

fof(f4729,plain,
    ( spl5_224
    | ~ spl5_174 ),
    inference(avatar_split_clause,[],[f2560,f2544,f4727])).

fof(f2560,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_174 ),
    inference(resolution,[],[f2545,f70])).

fof(f4561,plain,
    ( spl5_40
    | spl5_222
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f2063,f1113,f528,f137,f103,f4559,f309])).

fof(f4559,plain,
    ( spl5_222
  <=> ! [X1,X0,X2] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).

fof(f2063,plain,
    ( ! [X2,X0,X1] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f2062,f1556])).

fof(f2062,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),sK0)
        | v1_xboole_0(u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1955,f104])).

fof(f1955,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),sK0)
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1946,f1560])).

fof(f1560,plain,
    ( ! [X10,X11] : m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X10),X11),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f518])).

fof(f1946,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X0),X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(superposition,[],[f403,f1556])).

fof(f4466,plain,
    ( ~ spl5_219
    | spl5_220
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_118
    | ~ spl5_188 ),
    inference(avatar_split_clause,[],[f2891,f2877,f1826,f1113,f528,f4464,f4458])).

fof(f4458,plain,
    ( spl5_219
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_219])])).

fof(f4464,plain,
    ( spl5_220
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_220])])).

fof(f2891,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_118
    | ~ spl5_188 ),
    inference(forward_demodulation,[],[f2886,f1827])).

fof(f2886,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_188 ),
    inference(superposition,[],[f1627,f2878])).

fof(f1627,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 )
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1582,f1114])).

fof(f1582,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 )
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f1339])).

fof(f1339,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 )
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1323,f538])).

fof(f538,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 )
    | ~ spl5_52 ),
    inference(superposition,[],[f67,f529])).

fof(f1323,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1322,f1114])).

fof(f1322,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_52 ),
    inference(equality_resolution,[],[f535])).

fof(f535,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 )
    | ~ spl5_52 ),
    inference(superposition,[],[f68,f529])).

fof(f4424,plain,
    ( ~ spl5_215
    | spl5_216
    | spl5_213 ),
    inference(avatar_split_clause,[],[f4409,f4361,f4422,f4416])).

fof(f4416,plain,
    ( spl5_215
  <=> ~ m1_subset_1(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).

fof(f4422,plain,
    ( spl5_216
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_216])])).

fof(f4361,plain,
    ( spl5_213
  <=> ~ r2_hidden(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f4409,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ spl5_213 ),
    inference(resolution,[],[f4362,f79])).

fof(f4362,plain,
    ( ~ r2_hidden(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ spl5_213 ),
    inference(avatar_component_clause,[],[f4361])).

fof(f4363,plain,
    ( ~ spl5_213
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76
    | spl5_209 ),
    inference(avatar_split_clause,[],[f4312,f4171,f1113,f528,f137,f4361])).

fof(f4171,plain,
    ( spl5_209
  <=> ~ m1_subset_1(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f4312,plain,
    ( ~ r2_hidden(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_209 ),
    inference(resolution,[],[f4172,f1550])).

fof(f1550,plain,
    ( ! [X4] :
        ( m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f164])).

fof(f164,plain,
    ( ! [X4] :
        ( m1_subset_1(X4,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_12 ),
    inference(resolution,[],[f78,f138])).

fof(f4172,plain,
    ( ~ m1_subset_1(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0))
    | ~ spl5_209 ),
    inference(avatar_component_clause,[],[f4171])).

fof(f4347,plain,
    ( spl5_40
    | spl5_210
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1945,f1113,f528,f137,f103,f4345,f309])).

fof(f4345,plain,
    ( spl5_210
  <=> ! [X3,X2] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(sK1,X2),X3),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X2),X3),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).

fof(f1945,plain,
    ( ! [X2,X3] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(sK1,X2),X3),sK0)
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X2),X3),u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(resolution,[],[f1789,f79])).

fof(f1789,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,X6),X7),u1_pre_topc(sK0))
        | v3_pre_topc(k4_xboole_0(k4_xboole_0(sK1,X6),X7),sK0) )
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1788,f1555])).

fof(f1555,plain,
    ( ! [X17,X18] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X17),X18) = k4_xboole_0(k4_xboole_0(sK1,X17),X18)
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f401])).

fof(f1788,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,X6),X7),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X6),X7),sK0) )
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1787,f1553])).

fof(f1553,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f249])).

fof(f1787,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,X6),X7),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X6),X7),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK1,X6),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1771,f104])).

fof(f1771,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,X6),X7),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X6),X7),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK1,X6),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(superposition,[],[f197,f1555])).

fof(f4176,plain,
    ( spl5_206
    | spl5_208
    | ~ spl5_32
    | ~ spl5_58
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f2455,f1826,f573,f263,f4174,f4168])).

fof(f4168,plain,
    ( spl5_206
  <=> v1_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f4174,plain,
    ( spl5_208
  <=> m1_subset_1(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f2455,plain,
    ( m1_subset_1(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_32
    | ~ spl5_58
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f2454,f574])).

fof(f2454,plain,
    ( m1_subset_1(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f2453,f264])).

fof(f2453,plain,
    ( m1_subset_1(sK2(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_118 ),
    inference(superposition,[],[f767,f1827])).

fof(f767,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK3(X0)),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(sK3(X0))
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f333,f81])).

fof(f333,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK3(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(sK3(X0))
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f166,f79])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f84,f78])).

fof(f4071,plain,
    ( ~ spl5_175
    | spl5_204
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1086,f110,f4069,f2547])).

fof(f4069,plain,
    ( spl5_204
  <=> ! [X5,X4] :
        ( k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4))),sK3(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4))),X5) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4))),X5)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f1086,plain,
    ( ! [X4,X5] :
        ( k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4))),sK3(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4))),X5) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4))),X5)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4)))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1080,f376])).

fof(f1080,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X4)))
        | k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),u1_pre_topc(sK4),X4))),sK3(g1_pre_topc(u1_struct_0(sK4),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),u1_pre_topc(sK4),X4))),X5) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK4),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),u1_pre_topc(sK4),X4))),X5)
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f384,f376])).

fof(f384,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(g1_pre_topc(X4,k7_subset_1(k1_zfmisc_1(X4),X5,X6)))
      | k7_subset_1(u1_struct_0(g1_pre_topc(X4,k7_subset_1(k1_zfmisc_1(X4),X5,X6))),sK3(g1_pre_topc(X4,k7_subset_1(k1_zfmisc_1(X4),X5,X6))),X7) = k4_xboole_0(sK3(g1_pre_topc(X4,k7_subset_1(k1_zfmisc_1(X4),X5,X6))),X7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4))) ) ),
    inference(resolution,[],[f192,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X1,k7_subset_1(k1_zfmisc_1(X1),X0,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f83,f70])).

fof(f192,plain,(
    ! [X12,X11] :
      ( ~ l1_pre_topc(X11)
      | k7_subset_1(u1_struct_0(X11),sK3(X11),X12) = k4_xboole_0(sK3(X11),X12)
      | ~ v2_pre_topc(X11) ) ),
    inference(resolution,[],[f82,f84])).

fof(f4001,plain,
    ( ~ spl5_197
    | spl5_202
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f1643,f1376,f1113,f528,f263,f3999,f3658])).

fof(f3658,plain,
    ( spl5_197
  <=> ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).

fof(f3999,plain,
    ( spl5_202
  <=> m1_subset_1(sK2(k1_zfmisc_1(u1_struct_0(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).

fof(f1643,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(u1_struct_0(sK0))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f1604,f1548])).

fof(f1604,plain,
    ( ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(sK0))
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102 ),
    inference(backward_demodulation,[],[f1548,f1478])).

fof(f1478,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(subsumption_resolution,[],[f1424,f264])).

fof(f1424,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_102 ),
    inference(superposition,[],[f390,f1377])).

fof(f390,plain,(
    ! [X1] :
      ( m1_subset_1(sK2(k1_zfmisc_1(u1_struct_0(X1))),u1_pre_topc(X1))
      | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(X1))),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f206,f80])).

fof(f206,plain,(
    ! [X4] :
      ( r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(X4))),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(X4))),X4) ) ),
    inference(resolution,[],[f75,f81])).

fof(f3809,plain,
    ( ~ spl5_201
    | ~ spl5_2
    | spl5_199 ),
    inference(avatar_split_clause,[],[f3761,f3661,f103,f3807])).

fof(f3807,plain,
    ( spl5_201
  <=> ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f3661,plain,
    ( spl5_199
  <=> ~ r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).

fof(f3761,plain,
    ( ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK0)
    | ~ spl5_2
    | ~ spl5_199 ),
    inference(subsumption_resolution,[],[f3759,f104])).

fof(f3759,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK0)
    | ~ spl5_199 ),
    inference(resolution,[],[f3662,f206])).

fof(f3662,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(sK0))),u1_pre_topc(sK0))
    | ~ spl5_199 ),
    inference(avatar_component_clause,[],[f3661])).

fof(f3666,plain,
    ( ~ spl5_197
    | spl5_198
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f1641,f1376,f1113,f528,f263,f3664,f3658])).

fof(f3664,plain,
    ( spl5_198
  <=> r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f1641,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(sK0))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f1600,f1548])).

fof(f1600,plain,
    ( ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(sK0))
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102 ),
    inference(backward_demodulation,[],[f1548,f1449])).

fof(f1449,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(subsumption_resolution,[],[f1411,f264])).

fof(f1411,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(sK0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_102 ),
    inference(superposition,[],[f206,f1377])).

fof(f3302,plain,
    ( spl5_40
    | spl5_194
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f2080,f178,f103,f3300,f309])).

fof(f3300,plain,
    ( spl5_194
  <=> ! [X3] :
        ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X3),sK0)
        | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X3),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f2080,plain,
    ( ! [X3] :
        ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X3),sK0)
        | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X3),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f2079,f221])).

fof(f2079,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X3),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X3),sK0)
        | v1_xboole_0(u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f1028,f104])).

fof(f1028,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X3),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X3),sK0)
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f1012,f179])).

fof(f1012,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X3),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X3),sK0)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_18 ),
    inference(superposition,[],[f403,f221])).

fof(f3058,plain,
    ( spl5_40
    | spl5_192
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1242,f1239,f3056,f309])).

fof(f3056,plain,
    ( spl5_192
  <=> ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK3(sK0),X0),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK3(sK0),X0),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f1239,plain,
    ( spl5_96
  <=> ! [X1] :
        ( v3_pre_topc(k4_xboole_0(sK3(sK0),X1),sK0)
        | ~ r2_hidden(k4_xboole_0(sK3(sK0),X1),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f1242,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK3(sK0),X0),sK0)
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ m1_subset_1(k4_xboole_0(sK3(sK0),X0),u1_pre_topc(sK0)) )
    | ~ spl5_96 ),
    inference(resolution,[],[f1240,f79])).

fof(f1240,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(sK3(sK0),X1),u1_pre_topc(sK0))
        | v3_pre_topc(k4_xboole_0(sK3(sK0),X1),sK0) )
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f1239])).

fof(f2997,plain,
    ( ~ spl5_175
    | spl5_190
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f839,f110,f2995,f2547])).

fof(f2995,plain,
    ( spl5_190
  <=> ! [X22,X23] :
        ( v1_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X22))
        | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(X23,k4_xboole_0(u1_pre_topc(sK4),X22)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f839,plain,
    ( ! [X23,X22] :
        ( v1_xboole_0(k4_xboole_0(u1_pre_topc(sK4),X22))
        | ~ m1_subset_1(X23,k4_xboole_0(u1_pre_topc(sK4),X22))
        | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f823,f376])).

fof(f823,plain,
    ( ! [X23,X22] :
        ( ~ m1_subset_1(X23,k4_xboole_0(u1_pre_topc(sK4),X22))
        | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK4)))
        | v1_xboole_0(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK4)),u1_pre_topc(sK4),X22))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f356,f376])).

fof(f356,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k7_subset_1(X1,X0,X3))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(k7_subset_1(X1,X0,X3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f185,f79])).

fof(f185,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X8,k7_subset_1(X7,X6,X9))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | m1_subset_1(X8,X7) ) ),
    inference(resolution,[],[f83,f78])).

fof(f2879,plain,
    ( spl5_188
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f860,f110,f2877])).

fof(f860,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_4 ),
    inference(resolution,[],[f294,f111])).

fof(f294,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(subsumption_resolution,[],[f293,f155])).

fof(f155,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f76,f70])).

fof(f293,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(resolution,[],[f156,f73])).

fof(f156,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f76,f69])).

fof(f2795,plain,
    ( ~ spl5_175
    | spl5_186
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f665,f110,f2793,f2547])).

fof(f2793,plain,
    ( spl5_186
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,k4_xboole_0(u1_pre_topc(sK4),X2))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).

fof(f665,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(u1_pre_topc(sK4),X2))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f185,f376])).

fof(f2791,plain,
    ( ~ spl5_183
    | ~ spl5_175
    | spl5_184
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f666,f110,f2789,f2547,f2786])).

fof(f666,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k4_xboole_0(u1_pre_topc(sK4),X4))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f186,f376])).

fof(f2623,plain,
    ( ~ spl5_175
    | spl5_180
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f667,f110,f2621,f2547])).

fof(f667,plain,
    ( ! [X6] :
        ( m1_subset_1(k4_xboole_0(u1_pre_topc(sK4),X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f83,f376])).

fof(f2577,plain,
    ( ~ spl5_175
    | spl5_178
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f664,f110,f2575,f2547])).

fof(f2575,plain,
    ( spl5_178
  <=> ! [X1] : l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f664,plain,
    ( ! [X1] :
        ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X1)))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f183,f376])).

fof(f2555,plain,
    ( ~ spl5_4
    | spl5_175 ),
    inference(avatar_contradiction_clause,[],[f2554])).

fof(f2554,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_175 ),
    inference(subsumption_resolution,[],[f2553,f111])).

fof(f2553,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl5_175 ),
    inference(resolution,[],[f2548,f76])).

fof(f2548,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl5_175 ),
    inference(avatar_component_clause,[],[f2547])).

fof(f2552,plain,
    ( ~ spl5_175
    | spl5_176
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f663,f110,f2550,f2547])).

fof(f2550,plain,
    ( spl5_176
  <=> ! [X0] : v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f663,plain,
    ( ! [X0] :
        ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),k4_xboole_0(u1_pre_topc(sK4),X0)))
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f184,f376])).

fof(f184,plain,(
    ! [X4,X5,X3] :
      ( v1_pre_topc(g1_pre_topc(X4,k7_subset_1(k1_zfmisc_1(X4),X3,X5)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X4))) ) ),
    inference(resolution,[],[f83,f69])).

fof(f2442,plain,
    ( spl5_172
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f745,f110,f2440])).

fof(f745,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_4 ),
    inference(resolution,[],[f289,f111])).

fof(f289,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = k2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(resolution,[],[f155,f142])).

fof(f2424,plain,
    ( spl5_170
    | ~ spl5_167
    | spl5_164
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f720,f544,f110,f2252,f2258,f2422])).

fof(f2252,plain,
    ( spl5_164
  <=> v3_pre_topc(u1_struct_0(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f720,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK4)
    | ~ m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v1_xboole_0(u1_pre_topc(sK4))
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f719,f545])).

fof(f719,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v3_pre_topc(k2_struct_0(sK4),sK4)
    | v1_xboole_0(u1_pre_topc(sK4))
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f714,f111])).

fof(f714,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v3_pre_topc(k2_struct_0(sK4),sK4)
    | v1_xboole_0(u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl5_54 ),
    inference(superposition,[],[f324,f545])).

fof(f324,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(X0),u1_pre_topc(X0))
      | v3_pre_topc(k2_struct_0(X0),X0)
      | v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f202,f79])).

fof(f202,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(subsumption_resolution,[],[f196,f91])).

fof(f196,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(k2_struct_0(X0),u1_pre_topc(X0))
      | v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f74,f86])).

fof(f2319,plain,
    ( ~ spl5_77
    | spl5_168
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1084,f103,f2317,f1116])).

fof(f1116,plain,
    ( spl5_77
  <=> ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f2317,plain,
    ( spl5_168
  <=> ! [X1,X0] :
        ( k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0))),sK3(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0))),X1) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0))),X1)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_168])])).

fof(f1084,plain,
    ( ! [X0,X1] :
        ( k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0))),sK3(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0))),X1) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0))),X1)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0)))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1078,f375])).

fof(f375,plain,
    ( ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_pre_topc(sK0),X0) = k4_xboole_0(u1_pre_topc(sK0),X0)
    | ~ spl5_2 ),
    inference(resolution,[],[f187,f104])).

fof(f1078,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0)))
        | k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_pre_topc(sK0),X0))),sK3(g1_pre_topc(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_pre_topc(sK0),X0))),X1) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_pre_topc(sK0),X0))),X1)
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f384,f375])).

fof(f2263,plain,
    ( spl5_166
    | ~ spl5_165
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f643,f544,f110,f2249,f2261])).

fof(f2261,plain,
    ( spl5_166
  <=> m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f2249,plain,
    ( spl5_165
  <=> ~ v3_pre_topc(u1_struct_0(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f643,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK4)
    | m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f642,f545])).

fof(f642,plain,
    ( m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f636,f111])).

fof(f636,plain,
    ( m1_subset_1(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl5_54 ),
    inference(superposition,[],[f327,f545])).

fof(f2256,plain,
    ( spl5_162
    | ~ spl5_165
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f566,f544,f110,f2249,f2243])).

fof(f2243,plain,
    ( spl5_162
  <=> r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f566,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK4)
    | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f565,f545])).

fof(f565,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f560,f111])).

fof(f560,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl5_54 ),
    inference(superposition,[],[f209,f545])).

fof(f2254,plain,
    ( ~ spl5_163
    | spl5_164
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f564,f544,f110,f2252,f2246])).

fof(f564,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK4)
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f563,f545])).

fof(f563,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl5_4
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f559,f111])).

fof(f559,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl5_54 ),
    inference(superposition,[],[f202,f545])).

fof(f2241,plain,
    ( ~ spl5_149
    | ~ spl5_159
    | spl5_160
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f557,f544,f2239,f2236,f2171])).

fof(f2171,plain,
    ( spl5_149
  <=> ~ l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f557,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK4))
        | ~ v1_xboole_0(u1_struct_0(sK4))
        | ~ l1_struct_0(sK4) )
    | ~ spl5_54 ),
    inference(superposition,[],[f158,f545])).

fof(f2230,plain,
    ( spl5_156
    | ~ spl5_121
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1585,f1113,f579,f528,f263,f1930,f2228])).

fof(f2228,plain,
    ( spl5_156
  <=> ! [X2] :
        ( m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f1930,plain,
    ( spl5_121
  <=> ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f1585,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f1350])).

fof(f1350,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1323,f909])).

fof(f909,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_32
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f908,f580])).

fof(f908,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_32
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f897,f264])).

fof(f897,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_60 ),
    inference(superposition,[],[f412,f580])).

fof(f412,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k7_subset_1(u1_struct_0(X3),X4,X5),u1_pre_topc(X3))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X3),X4,X5),X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f204,f80])).

fof(f2215,plain,
    ( spl5_154
    | ~ spl5_121
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1583,f1113,f579,f528,f263,f1930,f2213])).

fof(f2213,plain,
    ( spl5_154
  <=> ! [X0] :
        ( r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f1583,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f1345])).

fof(f1345,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1323,f592])).

fof(f592,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_32
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f591,f580])).

fof(f591,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_32
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f586,f264])).

fof(f586,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_60 ),
    inference(superposition,[],[f204,f580])).

fof(f2209,plain,
    ( ~ spl5_121
    | spl5_152
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1626,f1113,f579,f528,f2207,f1930])).

fof(f2207,plain,
    ( spl5_152
  <=> ! [X5,X4] :
        ( m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4))
        | v1_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).

fof(f1626,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4))
        | ~ m1_subset_1(X5,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4)) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1569,f1548])).

fof(f1569,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4))
        | ~ m1_subset_1(X5,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4))
        | m1_subset_1(X5,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f828])).

fof(f828,plain,
    ( ! [X4,X5] :
        ( v1_xboole_0(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4))
        | ~ m1_subset_1(X5,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4))
        | m1_subset_1(X5,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f816,f580])).

fof(f816,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4))
        | m1_subset_1(X5,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v1_xboole_0(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_60 ),
    inference(superposition,[],[f356,f580])).

fof(f2182,plain,
    ( ~ spl5_4
    | spl5_149 ),
    inference(avatar_contradiction_clause,[],[f2181])).

fof(f2181,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_149 ),
    inference(subsumption_resolution,[],[f2180,f111])).

fof(f2180,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl5_149 ),
    inference(resolution,[],[f2172,f91])).

fof(f2172,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl5_149 ),
    inference(avatar_component_clause,[],[f2171])).

fof(f2179,plain,
    ( ~ spl5_149
    | spl5_150
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f554,f544,f2177,f2171])).

fof(f554,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_struct_0(sK4)
    | ~ spl5_54 ),
    inference(superposition,[],[f86,f545])).

fof(f2152,plain,
    ( ~ spl5_121
    | spl5_146
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1809,f1113,f579,f528,f103,f2150,f1930])).

fof(f2150,plain,
    ( spl5_146
  <=> ! [X3] :
        ( v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X3),sK0)
        | ~ r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X3),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f1809,plain,
    ( ! [X3] :
        ( v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X3),sK0)
        | ~ r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X3),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1808,f1562])).

fof(f1562,plain,
    ( ! [X10] : k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X10) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X10)
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f580])).

fof(f1808,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X3),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X3),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1795,f104])).

fof(f1795,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X3),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X3),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(superposition,[],[f197,f1562])).

fof(f2148,plain,
    ( ~ spl5_121
    | spl5_144
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1807,f1113,f579,f528,f103,f2146,f1930])).

fof(f2146,plain,
    ( spl5_144
  <=> ! [X2] :
        ( ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),sK0)
        | r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f1807,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),sK0)
        | r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1806,f1562])).

fof(f1806,plain,
    ( ! [X2] :
        ( r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1794,f104])).

fof(f1794,plain,
    ( ! [X2] :
        ( r2_hidden(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(superposition,[],[f204,f1562])).

fof(f2135,plain,
    ( ~ spl5_121
    | spl5_142
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1805,f1113,f579,f528,f103,f2133,f1930])).

fof(f2133,plain,
    ( spl5_142
  <=> ! [X1] :
        ( ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X1),sK0)
        | m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X1),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1805,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X1),sK0)
        | m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1804,f1562])).

fof(f1804,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X1),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X1),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1793,f104])).

fof(f1793,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X1),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X1),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(superposition,[],[f412,f1562])).

fof(f2131,plain,
    ( spl5_140
    | spl5_40
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2102,f1933,f1826,f1376,f1113,f579,f528,f263,f309,f2129])).

fof(f2129,plain,
    ( spl5_140
  <=> ! [X2] :
        ( v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f2102,plain,
    ( ! [X2] :
        ( v1_xboole_0(u1_pre_topc(sK0))
        | v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0)) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118
    | ~ spl5_120 ),
    inference(forward_demodulation,[],[f2101,f1377])).

fof(f2101,plain,
    ( ! [X2] :
        ( v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f2100,f1934])).

fof(f2100,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2099,f1827])).

fof(f2099,plain,
    ( ! [X2] :
        ( v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2098,f1562])).

fof(f2098,plain,
    ( ! [X2] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_32
    | ~ spl5_60
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2097,f1827])).

fof(f2097,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_32
    | ~ spl5_60
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f2096,f1377])).

fof(f2096,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_32
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f1011,f264])).

fof(f1011,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_60 ),
    inference(superposition,[],[f403,f580])).

fof(f2127,plain,
    ( spl5_40
    | spl5_132
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2068,f1933,f1113,f579,f528,f103,f2057,f309])).

fof(f2057,plain,
    ( spl5_132
  <=> ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f2068,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_120 ),
    inference(forward_demodulation,[],[f2067,f1562])).

fof(f2067,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),sK0)
        | v1_xboole_0(u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f2066,f104])).

fof(f2066,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),sK0)
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f1792,f1934])).

fof(f1792,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(superposition,[],[f403,f1562])).

fof(f2126,plain,
    ( spl5_138
    | spl5_40
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f2095,f1826,f1376,f1113,f528,f263,f137,f309,f2124])).

fof(f2124,plain,
    ( spl5_138
  <=> ! [X5,X4] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(sK1,X4),X5),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X4),X5),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f2095,plain,
    ( ! [X4,X5] :
        ( v1_xboole_0(u1_pre_topc(sK0))
        | v3_pre_topc(k4_xboole_0(k4_xboole_0(sK1,X4),X5),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X4),X5),u1_pre_topc(sK0)) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2094,f1377])).

fof(f2094,plain,
    ( ! [X4,X5] :
        ( v3_pre_topc(k4_xboole_0(k4_xboole_0(sK1,X4),X5),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X4),X5),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2093,f1555])).

fof(f2093,plain,
    ( ! [X4,X5] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X4),X5),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X4),X5),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2092,f1827])).

fof(f2092,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X4),X5),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(sK1,X4),X5),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f2091,f1377])).

fof(f2091,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X4),X5),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(sK1,X4),X5),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f1032,f264])).

fof(f1032,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X4),X5),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(sK1,X4),X5),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1013,f249])).

fof(f1013,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,X4),X5),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k4_xboole_0(sK1,X4),X5),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK1,X4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_12 ),
    inference(superposition,[],[f403,f401])).

fof(f2122,plain,
    ( spl5_136
    | spl5_40
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f2107,f1826,f1376,f1113,f528,f263,f137,f309,f2120])).

fof(f2120,plain,
    ( spl5_136
  <=> ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK1,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f2107,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_pre_topc(sK0))
        | v3_pre_topc(k4_xboole_0(sK1,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(sK0)) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2106,f1377])).

fof(f2106,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK1,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2105,f1551])).

fof(f1551,plain,
    ( ! [X8] : k7_subset_1(u1_struct_0(sK0),sK1,X8) = k4_xboole_0(sK1,X8)
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f190])).

fof(f2105,plain,
    ( ! [X0] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK1,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(sK0))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_102
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f2104,f1827])).

fof(f2104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f2103,f1377])).

fof(f2103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f1017,f264])).

fof(f1017,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1009,f138])).

fof(f1009,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_12 ),
    inference(superposition,[],[f403,f190])).

fof(f2118,plain,
    ( spl5_40
    | spl5_134
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1767,f1113,f528,f137,f130,f103,f2116,f309])).

fof(f2116,plain,
    ( spl5_134
  <=> ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK1,X0),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f1767,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK1,X0),sK0)
        | v1_xboole_0(u1_pre_topc(sK0))
        | ~ m1_subset_1(k4_xboole_0(sK1,X0),u1_pre_topc(sK0)) )
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(resolution,[],[f1708,f79])).

fof(f1708,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_xboole_0(sK1,X3),u1_pre_topc(sK0))
        | v3_pre_topc(k4_xboole_0(sK1,X3),sK0) )
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1707,f1551])).

fof(f1707,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_xboole_0(sK1,X3),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK0) )
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1706,f131])).

fof(f1706,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_xboole_0(sK1,X3),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1690,f104])).

fof(f1690,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_xboole_0(sK1,X3),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(superposition,[],[f197,f1551])).

fof(f2114,plain,
    ( spl5_40
    | ~ spl5_50
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f2113,f1376,f503,f309])).

fof(f503,plain,
    ( spl5_50
  <=> v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f2113,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl5_50
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f504,f1377])).

fof(f504,plain,
    ( v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f503])).

fof(f2059,plain,
    ( ~ spl5_121
    | spl5_132
    | ~ spl5_2
    | spl5_41
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1803,f1113,f579,f528,f306,f103,f2057,f1930])).

fof(f306,plain,
    ( spl5_41
  <=> ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1803,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_41
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1802,f1562])).

fof(f1802,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_41
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1801,f104])).

fof(f1801,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),sK0)
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_41
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1792,f307])).

fof(f307,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f306])).

fof(f2055,plain,
    ( spl5_128
    | spl5_130
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f939,f769,f2053,f2050])).

fof(f2050,plain,
    ( spl5_128
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f2053,plain,
    ( spl5_130
  <=> ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,sK3(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f769,plain,
    ( spl5_66
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f939,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK3(sK0))
        | ~ m1_subset_1(X0,sK3(sK0)) )
    | ~ spl5_66 ),
    inference(resolution,[],[f855,f79])).

fof(f855,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK3(sK0))
        | m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl5_66 ),
    inference(resolution,[],[f770,f78])).

fof(f770,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f769])).

fof(f2045,plain,
    ( ~ spl5_121
    | spl5_126
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1622,f1113,f579,f528,f2043,f1930])).

fof(f2043,plain,
    ( spl5_126
  <=> ! [X3,X2] :
        ( m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f1622,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2)) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1563,f1548])).

fof(f1563,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2))
        | m1_subset_1(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f588])).

fof(f588,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | m1_subset_1(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_60 ),
    inference(superposition,[],[f185,f580])).

fof(f2015,plain,
    ( ~ spl5_77
    | spl5_124
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f837,f103,f2013,f1116])).

fof(f2013,plain,
    ( spl5_124
  <=> ! [X18,X19] :
        ( v1_xboole_0(k4_xboole_0(u1_pre_topc(sK0),X18))
        | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,k4_xboole_0(u1_pre_topc(sK0),X18)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f837,plain,
    ( ! [X19,X18] :
        ( v1_xboole_0(k4_xboole_0(u1_pre_topc(sK0),X18))
        | ~ m1_subset_1(X19,k4_xboole_0(u1_pre_topc(sK0),X18))
        | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f821,f375])).

fof(f821,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(X19,k4_xboole_0(u1_pre_topc(sK0),X18))
        | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_pre_topc(sK0),X18))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f356,f375])).

fof(f1988,plain,
    ( spl5_122
    | ~ spl5_121
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1623,f1113,f579,f528,f1930,f1986])).

fof(f1623,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X6),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1564,f1548])).

fof(f1564,plain,
    ( ! [X6] :
        ( m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X6),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_52
    | ~ spl5_60
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f590])).

fof(f590,plain,
    ( ! [X6] :
        ( m1_subset_1(k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X6),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_60 ),
    inference(superposition,[],[f83,f580])).

fof(f1935,plain,
    ( spl5_120
    | ~ spl5_32
    | ~ spl5_58
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f1874,f1826,f573,f263,f1933])).

fof(f1874,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_32
    | ~ spl5_58
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f1873,f574])).

fof(f1873,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f1844,f264])).

fof(f1844,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_118 ),
    inference(superposition,[],[f84,f1827])).

fof(f1828,plain,
    ( spl5_118
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1548,f1113,f528,f1826])).

fof(f1725,plain,
    ( ~ spl5_117
    | ~ spl5_52
    | ~ spl5_76
    | spl5_107 ),
    inference(avatar_split_clause,[],[f1616,f1521,f1113,f528,f1723])).

fof(f1723,plain,
    ( spl5_117
  <=> ~ v3_pre_topc(u1_struct_0(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f1521,plain,
    ( spl5_107
  <=> ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f1616,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_52
    | ~ spl5_76
    | ~ spl5_107 ),
    inference(backward_demodulation,[],[f1548,f1522])).

fof(f1522,plain,
    ( ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_107 ),
    inference(avatar_component_clause,[],[f1521])).

fof(f1718,plain,
    ( spl5_114
    | ~ spl5_46
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1557,f1113,f528,f469,f1716])).

fof(f469,plain,
    ( spl5_46
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f1557,plain,
    ( u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_46
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f470])).

fof(f470,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f469])).

fof(f1675,plain,
    ( ~ spl5_113
    | ~ spl5_2
    | ~ spl5_10
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1665,f338,f130,f103,f1673])).

fof(f1673,plain,
    ( spl5_113
  <=> ~ v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f338,plain,
    ( spl5_43
  <=> ~ r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f1665,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f1664,f339])).

fof(f339,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f338])).

fof(f1664,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1657,f104])).

fof(f1657,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f131,f75])).

fof(f1656,plain,
    ( spl5_10
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1549,f1113,f528,f137,f130])).

fof(f1549,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1548,f138])).

fof(f1621,plain,
    ( spl5_11
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_contradiction_clause,[],[f1620])).

fof(f1620,plain,
    ( $false
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1549,f128])).

fof(f128,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_11
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1544,plain,
    ( spl5_106
    | ~ spl5_111
    | ~ spl5_32
    | ~ spl5_46
    | spl5_51
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1348,f1113,f528,f500,f469,f263,f1539,f1524])).

fof(f1524,plain,
    ( spl5_106
  <=> v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f1539,plain,
    ( spl5_111
  <=> ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f500,plain,
    ( spl5_51
  <=> ~ v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f1348,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_51
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1323,f718])).

fof(f718,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f717,f470])).

fof(f717,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f716,f264])).

fof(f716,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_46
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f713,f501])).

fof(f501,plain,
    ( ~ v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f500])).

fof(f713,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_46 ),
    inference(superposition,[],[f324,f470])).

fof(f1543,plain,
    ( ~ spl5_107
    | spl5_110
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1347,f1113,f528,f469,f263,f1536,f1521])).

fof(f1536,plain,
    ( spl5_110
  <=> m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f1347,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1323,f641])).

fof(f641,plain,
    ( ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_32
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f640,f470])).

fof(f640,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f635,f264])).

fof(f635,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_46 ),
    inference(superposition,[],[f327,f470])).

fof(f1542,plain,
    ( ~ spl5_107
    | spl5_108
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1329,f1113,f528,f469,f263,f1527,f1521])).

fof(f1527,plain,
    ( spl5_108
  <=> r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f1329,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1323,f492])).

fof(f492,plain,
    ( ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_32
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f491,f470])).

fof(f491,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f486,f264])).

fof(f486,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_46 ),
    inference(superposition,[],[f209,f470])).

fof(f1541,plain,
    ( ~ spl5_111
    | spl5_41
    | spl5_109 ),
    inference(avatar_split_clause,[],[f1534,f1530,f306,f1539])).

fof(f1530,plain,
    ( spl5_109
  <=> ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f1534,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ spl5_41
    | ~ spl5_109 ),
    inference(subsumption_resolution,[],[f1533,f307])).

fof(f1533,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ spl5_109 ),
    inference(resolution,[],[f1531,f79])).

fof(f1531,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ spl5_109 ),
    inference(avatar_component_clause,[],[f1530])).

fof(f1532,plain,
    ( spl5_106
    | ~ spl5_109
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1328,f1113,f528,f469,f263,f1530,f1524])).

fof(f1328,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1323,f490])).

fof(f490,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_32
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f489,f470])).

fof(f489,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f485,f264])).

fof(f485,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_46 ),
    inference(superposition,[],[f202,f470])).

fof(f1385,plain,
    ( spl5_104
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1336,f1113,f528,f1383])).

fof(f1383,plain,
    ( spl5_104
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f1336,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f1323,f529])).

fof(f1378,plain,
    ( spl5_102
    | ~ spl5_52
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1323,f1113,f528,f1376])).

fof(f1260,plain,
    ( ~ spl5_32
    | spl5_99 ),
    inference(avatar_contradiction_clause,[],[f1259])).

fof(f1259,plain,
    ( $false
    | ~ spl5_32
    | ~ spl5_99 ),
    inference(subsumption_resolution,[],[f1258,f264])).

fof(f1258,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_99 ),
    inference(resolution,[],[f1250,f91])).

fof(f1250,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f1249])).

fof(f1249,plain,
    ( spl5_99
  <=> ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f1257,plain,
    ( ~ spl5_99
    | spl5_100
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f480,f469,f1255,f1249])).

fof(f1255,plain,
    ( spl5_100
  <=> m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f480,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_46 ),
    inference(superposition,[],[f86,f470])).

fof(f1241,plain,
    ( ~ spl5_67
    | spl5_96
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f446,f103,f96,f1239,f772])).

fof(f772,plain,
    ( spl5_67
  <=> ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f96,plain,
    ( spl5_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f446,plain,
    ( ! [X1] :
        ( v3_pre_topc(k4_xboole_0(sK3(sK0),X1),sK0)
        | ~ r2_hidden(k4_xboole_0(sK3(sK0),X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f445,f387])).

fof(f387,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK3(sK0),X0) = k4_xboole_0(sK3(sK0),X0)
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f381,f97])).

fof(f97,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f96])).

fof(f381,plain,
    ( ! [X0] :
        ( k7_subset_1(u1_struct_0(sK0),sK3(sK0),X0) = k4_xboole_0(sK3(sK0),X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f192,f104])).

fof(f445,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(sK3(sK0),X1),u1_pre_topc(sK0))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(sK0),X1),sK0)
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f439,f104])).

fof(f439,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(sK3(sK0),X1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(sK0),X1),sK0)
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(superposition,[],[f197,f387])).

fof(f1236,plain,
    ( ~ spl5_67
    | spl5_94
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f444,f103,f96,f1234,f772])).

fof(f1234,plain,
    ( spl5_94
  <=> ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(sK3(sK0),X0),sK0)
        | r2_hidden(k4_xboole_0(sK3(sK0),X0),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(sK3(sK0),X0),sK0)
        | r2_hidden(k4_xboole_0(sK3(sK0),X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f443,f387])).

fof(f443,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(sK3(sK0),X0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(sK0),X0),sK0)
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f438,f104])).

fof(f438,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(sK3(sK0),X0),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),sK3(sK0),X0),sK0)
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(superposition,[],[f204,f387])).

fof(f1232,plain,
    ( ~ spl5_77
    | spl5_92
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f462,f103,f1230,f1116])).

fof(f1230,plain,
    ( spl5_92
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,k4_xboole_0(u1_pre_topc(sK0),X2))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f462,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(u1_pre_topc(sK0),X2))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f185,f375])).

fof(f1218,plain,
    ( ~ spl5_83
    | ~ spl5_77
    | spl5_90
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f463,f103,f1216,f1116,f1167])).

fof(f1167,plain,
    ( spl5_83
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f1216,plain,
    ( spl5_90
  <=> ! [X5,X4] : ~ r2_hidden(X5,k4_xboole_0(u1_pre_topc(sK0),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f463,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k4_xboole_0(u1_pre_topc(sK0),X4))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f186,f375])).

fof(f1181,plain,
    ( ~ spl5_77
    | spl5_88
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f464,f103,f1179,f1116])).

fof(f1179,plain,
    ( spl5_88
  <=> ! [X6] : m1_subset_1(k4_xboole_0(u1_pre_topc(sK0),X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f464,plain,
    ( ! [X6] :
        ( m1_subset_1(k4_xboole_0(u1_pre_topc(sK0),X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f83,f375])).

fof(f1177,plain,
    ( ~ spl5_67
    | spl5_86
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f440,f103,f96,f1175,f772])).

fof(f1175,plain,
    ( spl5_86
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,k4_xboole_0(sK3(sK0),X2))
        | m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f440,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(sK3(sK0),X2))
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(superposition,[],[f185,f387])).

fof(f1172,plain,
    ( ~ spl5_83
    | spl5_84
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1134,f1113,f1170,f1167])).

fof(f1170,plain,
    ( spl5_84
  <=> ! [X11] : ~ r2_hidden(X11,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f1134,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,u1_pre_topc(sK0))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_76 ),
    inference(resolution,[],[f1114,f77])).

fof(f1145,plain,
    ( ~ spl5_77
    | spl5_80
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f461,f103,f1143,f1116])).

fof(f1143,plain,
    ( spl5_80
  <=> ! [X1] : l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f461,plain,
    ( ! [X1] :
        ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X1)))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f183,f375])).

fof(f1124,plain,
    ( ~ spl5_2
    | spl5_77 ),
    inference(avatar_contradiction_clause,[],[f1123])).

fof(f1123,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_77 ),
    inference(subsumption_resolution,[],[f1122,f104])).

fof(f1122,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_77 ),
    inference(resolution,[],[f1117,f76])).

fof(f1117,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f1116])).

fof(f1121,plain,
    ( ~ spl5_77
    | spl5_78
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f460,f103,f1119,f1116])).

fof(f1119,plain,
    ( spl5_78
  <=> ! [X0] : v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f460,plain,
    ( ! [X0] :
        ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k4_xboole_0(u1_pre_topc(sK0),X0)))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f184,f375])).

fof(f1103,plain,
    ( ~ spl5_75
    | spl5_41
    | spl5_73 ),
    inference(avatar_split_clause,[],[f1071,f1002,f306,f1101])).

fof(f1101,plain,
    ( spl5_75
  <=> ~ m1_subset_1(sK3(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f1002,plain,
    ( spl5_73
  <=> ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f1071,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_41
    | ~ spl5_73 ),
    inference(subsumption_resolution,[],[f1070,f307])).

fof(f1070,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_73 ),
    inference(resolution,[],[f1003,f79])).

fof(f1003,plain,
    ( ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f1007,plain,
    ( ~ spl5_71
    | spl5_72
    | ~ spl5_2
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f857,f769,f103,f1005,f999])).

fof(f999,plain,
    ( spl5_71
  <=> ~ v3_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f1005,plain,
    ( spl5_72
  <=> r2_hidden(sK3(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f857,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f851,f104])).

fof(f851,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3(sK0),sK0)
    | ~ spl5_66 ),
    inference(resolution,[],[f770,f75])).

fof(f811,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_67 ),
    inference(avatar_contradiction_clause,[],[f810])).

fof(f810,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f809,f97])).

fof(f809,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f807,f104])).

fof(f807,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_67 ),
    inference(resolution,[],[f773,f84])).

fof(f773,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f772])).

fof(f777,plain,
    ( ~ spl5_67
    | spl5_68
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f442,f103,f96,f775,f772])).

fof(f775,plain,
    ( spl5_68
  <=> ! [X6] : m1_subset_1(k4_xboole_0(sK3(sK0),X6),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f442,plain,
    ( ! [X6] :
        ( m1_subset_1(k4_xboole_0(sK3(sK0),X6),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(superposition,[],[f83,f387])).

fof(f709,plain,
    ( ~ spl5_63
    | spl5_64
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f382,f110,f707,f704])).

fof(f704,plain,
    ( spl5_63
  <=> ~ v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f707,plain,
    ( spl5_64
  <=> ! [X1] : k7_subset_1(u1_struct_0(sK4),sK3(sK4),X1) = k4_xboole_0(sK3(sK4),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f382,plain,
    ( ! [X1] :
        ( k7_subset_1(u1_struct_0(sK4),sK3(sK4),X1) = k4_xboole_0(sK3(sK4),X1)
        | ~ v2_pre_topc(sK4) )
    | ~ spl5_4 ),
    inference(resolution,[],[f192,f111])).

fof(f585,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_59 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_59 ),
    inference(subsumption_resolution,[],[f583,f97])).

fof(f583,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_59 ),
    inference(subsumption_resolution,[],[f582,f104])).

fof(f582,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_59 ),
    inference(resolution,[],[f577,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',fc6_pre_topc)).

fof(f577,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl5_59
  <=> ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f581,plain,
    ( ~ spl5_59
    | spl5_60
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f386,f263,f579,f576])).

fof(f386,plain,
    ( ! [X10] :
        ( k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X10) = k4_xboole_0(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X10)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_32 ),
    inference(resolution,[],[f192,f264])).

fof(f553,plain,
    ( spl5_56
    | ~ spl5_32
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f539,f528,f263,f551])).

fof(f551,plain,
    ( spl5_56
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f539,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f531,f264])).

fof(f531,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_52 ),
    inference(superposition,[],[f156,f529])).

fof(f546,plain,
    ( spl5_54
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f145,f110,f544])).

fof(f145,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl5_4 ),
    inference(resolution,[],[f142,f111])).

fof(f530,plain,
    ( spl5_52
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f428,f103,f96,f528])).

fof(f428,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f422,f97])).

fof(f422,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f182,f104])).

fof(f182,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f181,f155])).

fof(f181,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f73,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f505,plain,
    ( ~ spl5_49
    | spl5_50
    | spl5_31 ),
    inference(avatar_split_clause,[],[f269,f260,f503,f497])).

fof(f497,plain,
    ( spl5_49
  <=> ~ m1_subset_1(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f260,plain,
    ( spl5_31
  <=> ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f269,plain,
    ( v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_31 ),
    inference(resolution,[],[f261,f79])).

fof(f261,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f260])).

fof(f471,plain,
    ( spl5_46
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f292,f263,f469])).

fof(f292,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_32 ),
    inference(resolution,[],[f264,f142])).

fof(f421,plain,
    ( spl5_34
    | ~ spl5_37
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f225,f178,f103,f278,f272])).

fof(f272,plain,
    ( spl5_34
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f278,plain,
    ( spl5_37
  <=> ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f225,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f220,f104])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl5_18 ),
    inference(resolution,[],[f179,f74])).

fof(f370,plain,
    ( ~ spl5_45
    | spl5_41
    | spl5_43 ),
    inference(avatar_split_clause,[],[f351,f338,f306,f368])).

fof(f368,plain,
    ( spl5_45
  <=> ~ m1_subset_1(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f351,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | ~ spl5_41
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f350,f307])).

fof(f350,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | ~ spl5_43 ),
    inference(resolution,[],[f339,f79])).

fof(f340,plain,
    ( ~ spl5_43
    | ~ spl5_2
    | spl5_11 ),
    inference(avatar_split_clause,[],[f322,f127,f103,f338])).

fof(f322,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f314,f104])).

fof(f314,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_11 ),
    inference(resolution,[],[f162,f128])).

fof(f311,plain,
    ( ~ spl5_39
    | spl5_40
    | spl5_37 ),
    inference(avatar_split_clause,[],[f295,f278,f309,f303])).

fof(f303,plain,
    ( spl5_39
  <=> ~ m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f295,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl5_37 ),
    inference(resolution,[],[f279,f79])).

fof(f279,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f278])).

fof(f291,plain,
    ( ~ spl5_2
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f288,f104])).

fof(f288,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_33 ),
    inference(resolution,[],[f155,f267])).

fof(f267,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl5_33
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f283,plain,
    ( ~ spl5_35
    | spl5_36
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f224,f178,f103,f281,f275])).

fof(f275,plain,
    ( spl5_35
  <=> ~ v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f281,plain,
    ( spl5_36
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f224,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f219,f104])).

fof(f219,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl5_18 ),
    inference(resolution,[],[f179,f75])).

fof(f270,plain,
    ( ~ spl5_29
    | spl5_30
    | ~ spl5_33
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f205,f137,f266,f257,f251])).

fof(f251,plain,
    ( spl5_29
  <=> ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f257,plain,
    ( spl5_30
  <=> r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f205,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_12 ),
    inference(resolution,[],[f75,f138])).

fof(f268,plain,
    ( spl5_28
    | ~ spl5_31
    | ~ spl5_33
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f198,f137,f266,f260,f254])).

fof(f254,plain,
    ( spl5_28
  <=> v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f198,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_12 ),
    inference(resolution,[],[f74,f138])).

fof(f247,plain,
    ( ~ spl5_25
    | spl5_26
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f223,f178,f245,f242])).

fof(f242,plain,
    ( spl5_25
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f245,plain,
    ( spl5_26
  <=> ! [X2] : ~ r2_hidden(X2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f223,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK0))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl5_18 ),
    inference(resolution,[],[f179,f77])).

fof(f237,plain,
    ( ~ spl5_21
    | spl5_22
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f159,f137,f235,f232])).

fof(f232,plain,
    ( spl5_21
  <=> ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f235,plain,
    ( spl5_22
  <=> ! [X4] : ~ r2_hidden(X4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f159,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_12 ),
    inference(resolution,[],[f77,f138])).

fof(f195,plain,
    ( ~ spl5_2
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f193,f104])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_17 ),
    inference(resolution,[],[f173,f91])).

fof(f173,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_17
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f180,plain,
    ( ~ spl5_17
    | spl5_18
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f161,f152,f178,f172])).

fof(f161,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl5_14 ),
    inference(superposition,[],[f86,f153])).

fof(f154,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f144,f103,f152])).

fof(f144,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f142,f104])).

fof(f141,plain,
    ( ~ spl5_11
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f64,f120,f134,f114,f127])).

fof(f134,plain,
    ( spl5_13
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f64,plain,
    ( ~ v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',t61_pre_topc)).

fof(f140,plain,
    ( spl5_10
    | spl5_12 ),
    inference(avatar_split_clause,[],[f61,f137,f130])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f139,plain,
    ( spl5_6
    | spl5_12 ),
    inference(avatar_split_clause,[],[f63,f137,f117])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f132,plain,
    ( spl5_10
    | spl5_8 ),
    inference(avatar_split_clause,[],[f60,f123,f130])).

fof(f60,plain,
    ( v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f125,plain,
    ( spl5_6
    | spl5_8 ),
    inference(avatar_split_clause,[],[f62,f123,f117])).

fof(f62,plain,
    ( v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f90,f110])).

fof(f90,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t61_pre_topc.p',existence_l1_pre_topc)).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f66,f103])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f65,f96])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
