%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t103_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:25 EDT 2019

% Result     : Theorem 0.68s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  708 (2400 expanded)
%              Number of leaves         :  203 (1013 expanded)
%              Depth                    :   10
%              Number of atoms          : 1635 (5449 expanded)
%              Number of equality atoms :   94 ( 325 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8957,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f135,f142,f149,f156,f169,f194,f231,f248,f284,f297,f338,f355,f364,f660,f678,f686,f719,f738,f786,f794,f814,f856,f863,f884,f946,f977,f986,f995,f1018,f1025,f1081,f1088,f1095,f1120,f1127,f1151,f1183,f1201,f1284,f1333,f1340,f1347,f1377,f1407,f1434,f1547,f1554,f1561,f1568,f1629,f1636,f1660,f1687,f1694,f1702,f2125,f2132,f2170,f2177,f2184,f2222,f2254,f2273,f2280,f2287,f2330,f2355,f2399,f2447,f2462,f2469,f2476,f2593,f2600,f2844,f2851,f2883,f2918,f2931,f2938,f2945,f2952,f2999,f3006,f3013,f3054,f3078,f3085,f3115,f3147,f3174,f3208,f3235,f3242,f3271,f3281,f3289,f3296,f3339,f3346,f3353,f3399,f3406,f3587,f3830,f3862,f3989,f4024,f4056,f4148,f4902,f4909,f4916,f4964,f4978,f5032,f5039,f5057,f5104,f5145,f5179,f5218,f5258,f5735,f7097,f7104,f7111,f7118,f7125,f7132,f7139,f7146,f7153,f7160,f7242,f7249,f7256,f7294,f7314,f7321,f7359,f7430,f7530,f7598,f7640,f7647,f7690,f7732,f7739,f7783,f7851,f7894,f7901,f7942,f7979,f7986,f8029,f8097,f8134,f8177,f8184,f8191,f8198,f8236,f8243,f8562,f8569,f8653,f8660,f8667,f8749,f8756,f8954,f8956])).

fof(f8956,plain,
    ( spl4_57
    | ~ spl4_308 ),
    inference(avatar_contradiction_clause,[],[f8955])).

fof(f8955,plain,
    ( $false
    | ~ spl4_57
    | ~ spl4_308 ),
    inference(subsumption_resolution,[],[f8911,f994])).

fof(f994,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f993])).

fof(f993,plain,
    ( spl4_57
  <=> ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f8911,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_308 ),
    inference(superposition,[],[f205,f7900])).

fof(f7900,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl4_308 ),
    inference(avatar_component_clause,[],[f7899])).

fof(f7899,plain,
    ( spl4_308
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_308])])).

fof(f205,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) ),
    inference(unit_resulting_resolution,[],[f177,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t3_subset)).

fof(f177,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f99,f100])).

fof(f100,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',commutativity_k3_xboole_0)).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t17_xboole_1)).

fof(f8954,plain,
    ( spl4_53
    | ~ spl4_308 ),
    inference(avatar_contradiction_clause,[],[f8953])).

fof(f8953,plain,
    ( $false
    | ~ spl4_53
    | ~ spl4_308 ),
    inference(subsumption_resolution,[],[f8909,f976])).

fof(f976,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f975])).

fof(f975,plain,
    ( spl4_53
  <=> ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f8909,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl4_308 ),
    inference(superposition,[],[f177,f7900])).

fof(f8756,plain,
    ( spl4_346
    | ~ spl4_4
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f1664,f1566,f140,f8754])).

fof(f8754,plain,
    ( spl4_346
  <=> m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_346])])).

fof(f140,plain,
    ( spl4_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1566,plain,
    ( spl4_98
  <=> m1_subset_1(k2_pre_topc(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f1664,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_98 ),
    inference(unit_resulting_resolution,[],[f141,f1567,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',dt_k2_tops_1)).

fof(f1567,plain,
    ( m1_subset_1(k2_pre_topc(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f1566])).

fof(f141,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f8749,plain,
    ( spl4_344
    | ~ spl4_4
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f1663,f1566,f140,f8747])).

fof(f8747,plain,
    ( spl4_344
  <=> m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_344])])).

fof(f1663,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_98 ),
    inference(unit_resulting_resolution,[],[f141,f1567,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',dt_k1_tops_1)).

fof(f8667,plain,
    ( spl4_342
    | ~ spl4_4
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1641,f1559,f140,f8665])).

fof(f8665,plain,
    ( spl4_342
  <=> m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_342])])).

fof(f1559,plain,
    ( spl4_96
  <=> m1_subset_1(k2_tops_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f1641,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_96 ),
    inference(unit_resulting_resolution,[],[f141,f1560,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',dt_k2_pre_topc)).

fof(f1560,plain,
    ( m1_subset_1(k2_tops_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f1559])).

fof(f8660,plain,
    ( spl4_340
    | ~ spl4_4
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1640,f1559,f140,f8658])).

fof(f8658,plain,
    ( spl4_340
  <=> m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_340])])).

fof(f1640,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_96 ),
    inference(unit_resulting_resolution,[],[f141,f1560,f107])).

fof(f8653,plain,
    ( spl4_338
    | ~ spl4_4
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1639,f1559,f140,f8651])).

fof(f8651,plain,
    ( spl4_338
  <=> m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_338])])).

fof(f1639,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_96 ),
    inference(unit_resulting_resolution,[],[f141,f1560,f106])).

fof(f8569,plain,
    ( spl4_336
    | ~ spl4_4
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f1608,f1545,f140,f8567])).

fof(f8567,plain,
    ( spl4_336
  <=> m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_336])])).

fof(f1545,plain,
    ( spl4_92
  <=> m1_subset_1(k1_tops_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f1608,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_92 ),
    inference(unit_resulting_resolution,[],[f141,f1546,f108])).

fof(f1546,plain,
    ( m1_subset_1(k1_tops_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f8562,plain,
    ( spl4_334
    | ~ spl4_4
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f1607,f1545,f140,f8560])).

fof(f8560,plain,
    ( spl4_334
  <=> m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_334])])).

fof(f1607,plain,
    ( m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_92 ),
    inference(unit_resulting_resolution,[],[f141,f1546,f107])).

fof(f8243,plain,
    ( spl4_332
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f1159,f1093,f8241])).

fof(f8241,plain,
    ( spl4_332
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_332])])).

fof(f1093,plain,
    ( spl4_66
  <=> m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f1159,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f1094,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',dt_k3_subset_1)).

fof(f1094,plain,
    ( m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f8236,plain,
    ( spl4_330
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1135,f1086,f8234])).

fof(f8234,plain,
    ( spl4_330
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_330])])).

fof(f1086,plain,
    ( spl4_64
  <=> m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f1135,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_64 ),
    inference(unit_resulting_resolution,[],[f1087,f104])).

fof(f1087,plain,
    ( m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f8198,plain,
    ( spl4_328
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1102,f1079,f8196])).

fof(f8196,plain,
    ( spl4_328
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_328])])).

fof(f1079,plain,
    ( spl4_62
  <=> m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1102,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_62 ),
    inference(unit_resulting_resolution,[],[f1080,f104])).

fof(f1080,plain,
    ( m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f8191,plain,
    ( spl4_326
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f770,f140,f133,f8189])).

fof(f8189,plain,
    ( spl4_326
  <=> m1_subset_1(k2_pre_topc(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_326])])).

fof(f133,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f770,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f275,f108])).

fof(f275,plain,
    ( ! [X0] : m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f202,f104])).

fof(f202,plain,
    ( ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f174,f112])).

fof(f174,plain,
    ( ! [X0] : r1_tarski(o_0_0_xboole_0,X0)
    | ~ spl4_2 ),
    inference(superposition,[],[f99,f160])).

fof(f160,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f157,f92])).

fof(f92,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t2_boole)).

fof(f157,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f134,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t6_boole)).

fof(f134,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f133])).

fof(f8184,plain,
    ( spl4_324
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f703,f140,f133,f8182])).

fof(f8182,plain,
    ( spl4_324
  <=> m1_subset_1(k2_tops_1(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_324])])).

fof(f703,plain,
    ( m1_subset_1(k2_tops_1(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f275,f107])).

fof(f8177,plain,
    ( spl4_322
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f644,f140,f133,f8175])).

fof(f8175,plain,
    ( spl4_322
  <=> m1_subset_1(k1_tops_1(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_322])])).

fof(f644,plain,
    ( m1_subset_1(k1_tops_1(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f275,f106])).

fof(f8134,plain,
    ( spl4_320
    | ~ spl4_282 ),
    inference(avatar_split_clause,[],[f8113,f7319,f8132])).

fof(f8132,plain,
    ( spl4_320
  <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_320])])).

fof(f7319,plain,
    ( spl4_282
  <=> m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_282])])).

fof(f8113,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_282 ),
    inference(unit_resulting_resolution,[],[f7320,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f7320,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_282 ),
    inference(avatar_component_clause,[],[f7319])).

fof(f8097,plain,
    ( spl4_318
    | ~ spl4_280 ),
    inference(avatar_split_clause,[],[f8072,f7312,f8095])).

fof(f8095,plain,
    ( spl4_318
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_318])])).

fof(f7312,plain,
    ( spl4_280
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_280])])).

fof(f8072,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_280 ),
    inference(unit_resulting_resolution,[],[f7313,f111])).

fof(f7313,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_280 ),
    inference(avatar_component_clause,[],[f7312])).

fof(f8029,plain,
    ( spl4_316
    | ~ spl4_276 ),
    inference(avatar_split_clause,[],[f8002,f7254,f8027])).

fof(f8027,plain,
    ( spl4_316
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_316])])).

fof(f7254,plain,
    ( spl4_276
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_276])])).

fof(f8002,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_276 ),
    inference(unit_resulting_resolution,[],[f7255,f111])).

fof(f7255,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_276 ),
    inference(avatar_component_clause,[],[f7254])).

fof(f7986,plain,
    ( spl4_314
    | ~ spl4_274 ),
    inference(avatar_split_clause,[],[f7958,f7247,f7984])).

fof(f7984,plain,
    ( spl4_314
  <=> r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_314])])).

fof(f7247,plain,
    ( spl4_274
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_274])])).

fof(f7958,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_274 ),
    inference(unit_resulting_resolution,[],[f7248,f111])).

fof(f7248,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_274 ),
    inference(avatar_component_clause,[],[f7247])).

fof(f7979,plain,
    ( spl4_312
    | ~ spl4_0
    | ~ spl4_24
    | ~ spl4_156 ),
    inference(avatar_split_clause,[],[f2958,f2916,f353,f126,f7977])).

fof(f7977,plain,
    ( spl4_312
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_312])])).

fof(f126,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f353,plain,
    ( spl4_24
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f2916,plain,
    ( spl4_156
  <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).

fof(f2958,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_24
    | ~ spl4_156 ),
    inference(subsumption_resolution,[],[f2954,f773])).

fof(f773,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f127,f354,f108])).

fof(f354,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f353])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f126])).

fof(f2954,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_156 ),
    inference(superposition,[],[f2917,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',redefinition_k9_subset_1)).

fof(f2917,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_156 ),
    inference(avatar_component_clause,[],[f2916])).

fof(f7942,plain,
    ( spl4_310
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f7917,f7240,f7940])).

fof(f7940,plain,
    ( spl4_310
  <=> r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_310])])).

fof(f7240,plain,
    ( spl4_272
  <=> m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_272])])).

fof(f7917,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_272 ),
    inference(unit_resulting_resolution,[],[f7241,f111])).

fof(f7241,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_272 ),
    inference(avatar_component_clause,[],[f7240])).

fof(f7901,plain,
    ( spl4_308
    | ~ spl4_8
    | ~ spl4_156 ),
    inference(avatar_split_clause,[],[f2953,f2916,f154,f7899])).

fof(f154,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f2953,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl4_8
    | ~ spl4_156 ),
    inference(superposition,[],[f2917,f554])).

fof(f554,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f536,f466])).

fof(f466,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f155,f117])).

fof(f155,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f536,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f155,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',commutativity_k9_subset_1)).

fof(f7894,plain,
    ( spl4_306
    | ~ spl4_270 ),
    inference(avatar_split_clause,[],[f7867,f7158,f7892])).

fof(f7892,plain,
    ( spl4_306
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_306])])).

fof(f7158,plain,
    ( spl4_270
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_270])])).

fof(f7867,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_270 ),
    inference(unit_resulting_resolution,[],[f7159,f111])).

fof(f7159,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_270 ),
    inference(avatar_component_clause,[],[f7158])).

fof(f7851,plain,
    ( spl4_304
    | ~ spl4_268 ),
    inference(avatar_split_clause,[],[f7830,f7151,f7849])).

fof(f7849,plain,
    ( spl4_304
  <=> r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_304])])).

fof(f7151,plain,
    ( spl4_268
  <=> m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_268])])).

fof(f7830,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_268 ),
    inference(unit_resulting_resolution,[],[f7152,f111])).

fof(f7152,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_268 ),
    inference(avatar_component_clause,[],[f7151])).

fof(f7783,plain,
    ( spl4_302
    | ~ spl4_266 ),
    inference(avatar_split_clause,[],[f7755,f7144,f7781])).

fof(f7781,plain,
    ( spl4_302
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_302])])).

fof(f7144,plain,
    ( spl4_266
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_266])])).

fof(f7755,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_266 ),
    inference(unit_resulting_resolution,[],[f7145,f111])).

fof(f7145,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_266 ),
    inference(avatar_component_clause,[],[f7144])).

fof(f7739,plain,
    ( spl4_300
    | ~ spl4_262 ),
    inference(avatar_split_clause,[],[f7706,f7130,f7737])).

fof(f7737,plain,
    ( spl4_300
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_300])])).

fof(f7130,plain,
    ( spl4_262
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_262])])).

fof(f7706,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_262 ),
    inference(unit_resulting_resolution,[],[f7131,f111])).

fof(f7131,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_262 ),
    inference(avatar_component_clause,[],[f7130])).

fof(f7732,plain,
    ( spl4_298
    | ~ spl4_0
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f1959,f1685,f126,f7730])).

fof(f7730,plain,
    ( spl4_298
  <=> m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_298])])).

fof(f1685,plain,
    ( spl4_106
  <=> m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f1959,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_106 ),
    inference(unit_resulting_resolution,[],[f127,f1686,f107])).

fof(f1686,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f1685])).

fof(f7690,plain,
    ( spl4_296
    | ~ spl4_260 ),
    inference(avatar_split_clause,[],[f7663,f7123,f7688])).

fof(f7688,plain,
    ( spl4_296
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_296])])).

fof(f7123,plain,
    ( spl4_260
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_260])])).

fof(f7663,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_260 ),
    inference(unit_resulting_resolution,[],[f7124,f111])).

fof(f7124,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_260 ),
    inference(avatar_component_clause,[],[f7123])).

fof(f7647,plain,
    ( spl4_294
    | ~ spl4_0
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f1958,f1685,f126,f7645])).

fof(f7645,plain,
    ( spl4_294
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_294])])).

fof(f1958,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_106 ),
    inference(unit_resulting_resolution,[],[f127,f1686,f106])).

fof(f7640,plain,
    ( spl4_292
    | ~ spl4_258 ),
    inference(avatar_split_clause,[],[f7614,f7116,f7638])).

fof(f7638,plain,
    ( spl4_292
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_292])])).

fof(f7116,plain,
    ( spl4_258
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_258])])).

fof(f7614,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_258 ),
    inference(unit_resulting_resolution,[],[f7117,f111])).

fof(f7117,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_258 ),
    inference(avatar_component_clause,[],[f7116])).

fof(f7598,plain,
    ( spl4_290
    | ~ spl4_256 ),
    inference(avatar_split_clause,[],[f7577,f7109,f7596])).

fof(f7596,plain,
    ( spl4_290
  <=> r1_tarski(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_290])])).

fof(f7109,plain,
    ( spl4_256
  <=> m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_256])])).

fof(f7577,plain,
    ( r1_tarski(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_256 ),
    inference(unit_resulting_resolution,[],[f7110,f111])).

fof(f7110,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_256 ),
    inference(avatar_component_clause,[],[f7109])).

fof(f7530,plain,
    ( spl4_288
    | ~ spl4_254 ),
    inference(avatar_split_clause,[],[f7505,f7102,f7528])).

fof(f7528,plain,
    ( spl4_288
  <=> r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_288])])).

fof(f7102,plain,
    ( spl4_254
  <=> m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_254])])).

fof(f7505,plain,
    ( r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_254 ),
    inference(unit_resulting_resolution,[],[f7103,f111])).

fof(f7103,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_254 ),
    inference(avatar_component_clause,[],[f7102])).

fof(f7430,plain,
    ( spl4_286
    | ~ spl4_0
    | ~ spl4_102 ),
    inference(avatar_split_clause,[],[f1811,f1634,f126,f7428])).

fof(f7428,plain,
    ( spl4_286
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_286])])).

fof(f1634,plain,
    ( spl4_102
  <=> m1_subset_1(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f1811,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_102 ),
    inference(unit_resulting_resolution,[],[f127,f1635,f108])).

fof(f1635,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f7359,plain,
    ( spl4_284
    | ~ spl4_0
    | ~ spl4_102 ),
    inference(avatar_split_clause,[],[f1810,f1634,f126,f7357])).

fof(f7357,plain,
    ( spl4_284
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_284])])).

fof(f1810,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_102 ),
    inference(unit_resulting_resolution,[],[f127,f1635,f107])).

fof(f7321,plain,
    ( spl4_282
    | ~ spl4_0
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f1411,f1345,f126,f7319])).

fof(f1345,plain,
    ( spl4_84
  <=> m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f1411,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_84 ),
    inference(unit_resulting_resolution,[],[f127,f1346,f107])).

fof(f1346,plain,
    ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f7314,plain,
    ( spl4_280
    | ~ spl4_0
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f1410,f1345,f126,f7312])).

fof(f1410,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_84 ),
    inference(unit_resulting_resolution,[],[f127,f1346,f106])).

fof(f7294,plain,
    ( spl4_278
    | ~ spl4_0
    | ~ spl4_102 ),
    inference(avatar_split_clause,[],[f1809,f1634,f126,f7292])).

fof(f7292,plain,
    ( spl4_278
  <=> m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_278])])).

fof(f1809,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_102 ),
    inference(unit_resulting_resolution,[],[f127,f1635,f106])).

fof(f7256,plain,
    ( spl4_276
    | ~ spl4_0
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f1382,f1338,f126,f7254])).

fof(f1338,plain,
    ( spl4_82
  <=> m1_subset_1(k2_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1382,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_82 ),
    inference(unit_resulting_resolution,[],[f127,f1339,f108])).

fof(f1339,plain,
    ( m1_subset_1(k2_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f7249,plain,
    ( spl4_274
    | ~ spl4_0
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f1381,f1338,f126,f7247])).

fof(f1381,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_82 ),
    inference(unit_resulting_resolution,[],[f127,f1339,f107])).

fof(f7242,plain,
    ( spl4_272
    | ~ spl4_0
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f1380,f1338,f126,f7240])).

fof(f1380,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_82 ),
    inference(unit_resulting_resolution,[],[f127,f1339,f106])).

fof(f7160,plain,
    ( spl4_270
    | ~ spl4_0
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1356,f1331,f126,f7158])).

fof(f1331,plain,
    ( spl4_80
  <=> m1_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1356,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_80 ),
    inference(unit_resulting_resolution,[],[f127,f1332,f108])).

fof(f1332,plain,
    ( m1_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1331])).

fof(f7153,plain,
    ( spl4_268
    | ~ spl4_0
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1355,f1331,f126,f7151])).

fof(f1355,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_80 ),
    inference(unit_resulting_resolution,[],[f127,f1332,f107])).

fof(f7146,plain,
    ( spl4_266
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f928,f861,f7144])).

fof(f861,plain,
    ( spl4_46
  <=> m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f928,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f862,f104])).

fof(f862,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f861])).

fof(f7139,plain,
    ( spl4_264
    | ~ spl4_0
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1738,f1552,f126,f7137])).

fof(f7137,plain,
    ( spl4_264
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_264])])).

fof(f1552,plain,
    ( spl4_94
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f1738,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_94 ),
    inference(unit_resulting_resolution,[],[f127,f1553,f108])).

fof(f1553,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f1552])).

fof(f7132,plain,
    ( spl4_262
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f868,f854,f7130])).

fof(f854,plain,
    ( spl4_44
  <=> m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f868,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f855,f104])).

fof(f855,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f854])).

fof(f7125,plain,
    ( spl4_260
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f769,f133,f126,f7123])).

fof(f769,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f127,f275,f108])).

fof(f7118,plain,
    ( spl4_258
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f742,f684,f7116])).

fof(f684,plain,
    ( spl4_32
  <=> m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f742,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f685,f104])).

fof(f685,plain,
    ( m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f684])).

fof(f7111,plain,
    ( spl4_256
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f702,f133,f126,f7109])).

fof(f702,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f127,f275,f107])).

fof(f7104,plain,
    ( spl4_254
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f643,f133,f126,f7102])).

fof(f643,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f127,f275,f106])).

fof(f7097,plain,
    ( spl4_252
    | ~ spl4_0
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1737,f1552,f126,f7095])).

fof(f7095,plain,
    ( spl4_252
  <=> m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_252])])).

fof(f1737,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_94 ),
    inference(unit_resulting_resolution,[],[f127,f1553,f107])).

fof(f5735,plain,
    ( ~ spl4_251
    | spl4_57 ),
    inference(avatar_split_clause,[],[f1007,f993,f5733])).

fof(f5733,plain,
    ( spl4_251
  <=> ~ r2_hidden(k2_tops_1(sK0,sK1),k3_subset_1(k1_zfmisc_1(sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_251])])).

fof(f1007,plain,
    ( ~ r2_hidden(k2_tops_1(sK0,sK1),k3_subset_1(k1_zfmisc_1(sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(sK1)))))
    | ~ spl4_57 ),
    inference(unit_resulting_resolution,[],[f277,f994,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t4_subset)).

fof(f277,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f97,f104])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',existence_m1_subset_1)).

fof(f5258,plain,
    ( spl4_248
    | ~ spl4_232 ),
    inference(avatar_split_clause,[],[f5234,f5030,f5256])).

fof(f5256,plain,
    ( spl4_248
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_248])])).

fof(f5030,plain,
    ( spl4_232
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_232])])).

fof(f5234,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_232 ),
    inference(unit_resulting_resolution,[],[f5031,f111])).

fof(f5031,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_232 ),
    inference(avatar_component_clause,[],[f5030])).

fof(f5218,plain,
    ( spl4_246
    | ~ spl4_230 ),
    inference(avatar_split_clause,[],[f5195,f4976,f5216])).

fof(f5216,plain,
    ( spl4_246
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_246])])).

fof(f4976,plain,
    ( spl4_230
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_230])])).

fof(f5195,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_230 ),
    inference(unit_resulting_resolution,[],[f4977,f111])).

fof(f4977,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_230 ),
    inference(avatar_component_clause,[],[f4976])).

fof(f5179,plain,
    ( spl4_244
    | ~ spl4_228 ),
    inference(avatar_split_clause,[],[f5161,f4962,f5177])).

fof(f5177,plain,
    ( spl4_244
  <=> r1_tarski(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_244])])).

fof(f4962,plain,
    ( spl4_228
  <=> m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).

fof(f5161,plain,
    ( r1_tarski(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_228 ),
    inference(unit_resulting_resolution,[],[f4963,f111])).

fof(f4963,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_228 ),
    inference(avatar_component_clause,[],[f4962])).

fof(f5145,plain,
    ( spl4_242
    | ~ spl4_226 ),
    inference(avatar_split_clause,[],[f5120,f4914,f5143])).

fof(f5143,plain,
    ( spl4_242
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_242])])).

fof(f4914,plain,
    ( spl4_226
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_226])])).

fof(f5120,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_226 ),
    inference(unit_resulting_resolution,[],[f4915,f111])).

fof(f4915,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_226 ),
    inference(avatar_component_clause,[],[f4914])).

fof(f5104,plain,
    ( spl4_240
    | ~ spl4_222 ),
    inference(avatar_split_clause,[],[f5075,f4900,f5102])).

fof(f5102,plain,
    ( spl4_240
  <=> r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_240])])).

fof(f4900,plain,
    ( spl4_222
  <=> m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_222])])).

fof(f5075,plain,
    ( r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_222 ),
    inference(unit_resulting_resolution,[],[f4901,f111])).

fof(f4901,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_222 ),
    inference(avatar_component_clause,[],[f4900])).

fof(f5057,plain,
    ( spl4_236
    | ~ spl4_239
    | ~ spl4_0
    | ~ spl4_28
    | ~ spl4_60
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f1400,f1282,f1023,f658,f126,f5055,f5049])).

fof(f5049,plain,
    ( spl4_236
  <=> v5_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_236])])).

fof(f5055,plain,
    ( spl4_239
  <=> k1_tops_1(sK0,sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_239])])).

fof(f658,plain,
    ( spl4_28
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1023,plain,
    ( spl4_60
  <=> k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f1282,plain,
    ( spl4_78
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f1400,plain,
    ( k1_tops_1(sK0,sK1) != sK1
    | v5_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_0
    | ~ spl4_28
    | ~ spl4_60
    | ~ spl4_78 ),
    inference(forward_demodulation,[],[f1399,f1024])).

fof(f1024,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f1023])).

fof(f1399,plain,
    ( k1_tops_1(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | v5_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_0
    | ~ spl4_28
    | ~ spl4_78 ),
    inference(subsumption_resolution,[],[f1398,f127])).

fof(f1398,plain,
    ( k1_tops_1(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | v5_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_78 ),
    inference(subsumption_resolution,[],[f1395,f659])).

fof(f659,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f658])).

fof(f1395,plain,
    ( k1_tops_1(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | v5_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_78 ),
    inference(superposition,[],[f96,f1283])).

fof(f1283,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',d7_tops_1)).

fof(f5039,plain,
    ( spl4_234
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1059,f140,f5037])).

fof(f5037,plain,
    ( spl4_234
  <=> k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k9_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k2_pre_topc(sK3,k3_subset_1(u1_struct_0(sK3),sK2(k1_zfmisc_1(u1_struct_0(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_234])])).

fof(f1059,plain,
    ( k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k9_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k2_pre_topc(sK3,k3_subset_1(u1_struct_0(sK3),sK2(k1_zfmisc_1(u1_struct_0(sK3))))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f97,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',d2_tops_1)).

fof(f5032,plain,
    ( spl4_232
    | ~ spl4_0
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f773,f353,f126,f5030])).

fof(f4978,plain,
    ( spl4_230
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f722,f717,f4976])).

fof(f717,plain,
    ( spl4_34
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f722,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f718,f104])).

fof(f718,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f717])).

fof(f4964,plain,
    ( spl4_228
    | ~ spl4_0
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f706,f353,f126,f4962])).

fof(f706,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f127,f354,f107])).

fof(f4916,plain,
    ( spl4_226
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f662,f658,f4914])).

fof(f662,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f659,f104])).

fof(f4909,plain,
    ( spl4_224
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f1058,f126,f4907])).

fof(f4907,plain,
    ( spl4_224
  <=> k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).

fof(f1058,plain,
    ( k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f97,f94])).

fof(f4902,plain,
    ( spl4_222
    | ~ spl4_0
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f647,f353,f126,f4900])).

fof(f647,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f127,f354,f106])).

fof(f4148,plain,
    ( spl4_220
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f4130,f3404,f4146])).

fof(f4146,plain,
    ( spl4_220
  <=> r1_tarski(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_220])])).

fof(f3404,plain,
    ( spl4_206
  <=> m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f4130,plain,
    ( r1_tarski(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),u1_struct_0(sK3))
    | ~ spl4_206 ),
    inference(unit_resulting_resolution,[],[f3405,f111])).

fof(f3405,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_206 ),
    inference(avatar_component_clause,[],[f3404])).

fof(f4056,plain,
    ( spl4_218
    | ~ spl4_204 ),
    inference(avatar_split_clause,[],[f4036,f3397,f4054])).

fof(f4054,plain,
    ( spl4_218
  <=> r1_tarski(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_218])])).

fof(f3397,plain,
    ( spl4_204
  <=> m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_204])])).

fof(f4036,plain,
    ( r1_tarski(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),u1_struct_0(sK3))
    | ~ spl4_204 ),
    inference(unit_resulting_resolution,[],[f3398,f111])).

fof(f3398,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_204 ),
    inference(avatar_component_clause,[],[f3397])).

fof(f4024,plain,
    ( spl4_216
    | ~ spl4_202 ),
    inference(avatar_split_clause,[],[f4001,f3351,f4022])).

fof(f4022,plain,
    ( spl4_216
  <=> r1_tarski(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_216])])).

fof(f3351,plain,
    ( spl4_202
  <=> m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).

fof(f4001,plain,
    ( r1_tarski(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3))
    | ~ spl4_202 ),
    inference(unit_resulting_resolution,[],[f3352,f111])).

fof(f3352,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_202 ),
    inference(avatar_component_clause,[],[f3351])).

fof(f3989,plain,
    ( spl4_214
    | ~ spl4_200 ),
    inference(avatar_split_clause,[],[f3971,f3344,f3987])).

fof(f3987,plain,
    ( spl4_214
  <=> r1_tarski(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_214])])).

fof(f3344,plain,
    ( spl4_200
  <=> m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).

fof(f3971,plain,
    ( r1_tarski(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3))
    | ~ spl4_200 ),
    inference(unit_resulting_resolution,[],[f3345,f111])).

fof(f3345,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_200 ),
    inference(avatar_component_clause,[],[f3344])).

fof(f3862,plain,
    ( spl4_212
    | ~ spl4_198 ),
    inference(avatar_split_clause,[],[f3842,f3337,f3860])).

fof(f3860,plain,
    ( spl4_212
  <=> r1_tarski(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_212])])).

fof(f3337,plain,
    ( spl4_198
  <=> m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).

fof(f3842,plain,
    ( r1_tarski(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3))
    | ~ spl4_198 ),
    inference(unit_resulting_resolution,[],[f3338,f111])).

fof(f3338,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_198 ),
    inference(avatar_component_clause,[],[f3337])).

fof(f3830,plain,
    ( spl4_210
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f3809,f3294,f3828])).

fof(f3828,plain,
    ( spl4_210
  <=> r1_tarski(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_210])])).

fof(f3294,plain,
    ( spl4_196
  <=> m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).

fof(f3809,plain,
    ( r1_tarski(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3))
    | ~ spl4_196 ),
    inference(unit_resulting_resolution,[],[f3295,f111])).

fof(f3295,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_196 ),
    inference(avatar_component_clause,[],[f3294])).

fof(f3587,plain,
    ( spl4_208
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f3571,f3287,f3585])).

fof(f3585,plain,
    ( spl4_208
  <=> r1_tarski(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_208])])).

fof(f3287,plain,
    ( spl4_194
  <=> m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f3571,plain,
    ( r1_tarski(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),u1_struct_0(sK3))
    | ~ spl4_194 ),
    inference(unit_resulting_resolution,[],[f3288,f111])).

fof(f3288,plain,
    ( m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_194 ),
    inference(avatar_component_clause,[],[f3287])).

fof(f3406,plain,
    ( spl4_206
    | ~ spl4_4
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f1155,f1093,f140,f3404])).

fof(f1155,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f141,f1094,f107])).

fof(f3399,plain,
    ( spl4_204
    | ~ spl4_4
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f1154,f1093,f140,f3397])).

fof(f1154,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f141,f1094,f106])).

fof(f3353,plain,
    ( spl4_202
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1132,f1086,f140,f3351])).

fof(f1132,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(unit_resulting_resolution,[],[f141,f1087,f108])).

fof(f3346,plain,
    ( spl4_200
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1131,f1086,f140,f3344])).

fof(f1131,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(unit_resulting_resolution,[],[f141,f1087,f107])).

fof(f3339,plain,
    ( spl4_198
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1130,f1086,f140,f3337])).

fof(f1130,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(unit_resulting_resolution,[],[f141,f1087,f106])).

fof(f3296,plain,
    ( spl4_196
    | ~ spl4_4
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1099,f1079,f140,f3294])).

fof(f1099,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_62 ),
    inference(unit_resulting_resolution,[],[f141,f1080,f108])).

fof(f3289,plain,
    ( spl4_194
    | ~ spl4_4
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1098,f1079,f140,f3287])).

fof(f1098,plain,
    ( m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_62 ),
    inference(unit_resulting_resolution,[],[f141,f1080,f107])).

fof(f3281,plain,
    ( spl4_192
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f913,f140,f3279])).

fof(f3279,plain,
    ( spl4_192
  <=> k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k1_tops_1(sK3,k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f913,plain,
    ( k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k1_tops_1(sK3,k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f97,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',projectivity_k1_tops_1)).

fof(f3271,plain,
    ( spl4_190
    | ~ spl4_168 ),
    inference(avatar_split_clause,[],[f3254,f3004,f3269])).

fof(f3269,plain,
    ( spl4_190
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_190])])).

fof(f3004,plain,
    ( spl4_168
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_168])])).

fof(f3254,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_168 ),
    inference(unit_resulting_resolution,[],[f3005,f111])).

fof(f3005,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_168 ),
    inference(avatar_component_clause,[],[f3004])).

fof(f3242,plain,
    ( spl4_188
    | ~ spl4_166 ),
    inference(avatar_split_clause,[],[f3220,f2997,f3240])).

fof(f3240,plain,
    ( spl4_188
  <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).

fof(f2997,plain,
    ( spl4_166
  <=> m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).

fof(f3220,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_166 ),
    inference(unit_resulting_resolution,[],[f2998,f111])).

fof(f2998,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_166 ),
    inference(avatar_component_clause,[],[f2997])).

fof(f3235,plain,
    ( spl4_186
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f842,f140,f3233])).

fof(f3233,plain,
    ( spl4_186
  <=> k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k2_pre_topc(sK3,k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_186])])).

fof(f842,plain,
    ( k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k2_pre_topc(sK3,k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f97,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',projectivity_k2_pre_topc)).

fof(f3208,plain,
    ( spl4_184
    | ~ spl4_164 ),
    inference(avatar_split_clause,[],[f3191,f2950,f3206])).

fof(f3206,plain,
    ( spl4_184
  <=> r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_184])])).

fof(f2950,plain,
    ( spl4_164
  <=> m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f3191,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_164 ),
    inference(unit_resulting_resolution,[],[f2951,f111])).

fof(f2951,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_164 ),
    inference(avatar_component_clause,[],[f2950])).

fof(f3174,plain,
    ( spl4_182
    | ~ spl4_162 ),
    inference(avatar_split_clause,[],[f3159,f2943,f3172])).

fof(f3172,plain,
    ( spl4_182
  <=> r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f2943,plain,
    ( spl4_162
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f3159,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_162 ),
    inference(unit_resulting_resolution,[],[f2944,f111])).

fof(f2944,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_162 ),
    inference(avatar_component_clause,[],[f2943])).

fof(f3147,plain,
    ( spl4_180
    | ~ spl4_160 ),
    inference(avatar_split_clause,[],[f3129,f2936,f3145])).

fof(f3145,plain,
    ( spl4_180
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_180])])).

fof(f2936,plain,
    ( spl4_160
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f3129,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_160 ),
    inference(unit_resulting_resolution,[],[f2937,f111])).

fof(f2937,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_160 ),
    inference(avatar_component_clause,[],[f2936])).

fof(f3115,plain,
    ( spl4_178
    | ~ spl4_158 ),
    inference(avatar_split_clause,[],[f3097,f2929,f3113])).

fof(f3113,plain,
    ( spl4_178
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).

fof(f2929,plain,
    ( spl4_158
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).

fof(f3097,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_158 ),
    inference(unit_resulting_resolution,[],[f2930,f111])).

fof(f2930,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_158 ),
    inference(avatar_component_clause,[],[f2929])).

fof(f3085,plain,
    ( spl4_176
    | ~ spl4_154 ),
    inference(avatar_split_clause,[],[f3063,f2881,f3083])).

fof(f3083,plain,
    ( spl4_176
  <=> r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_176])])).

fof(f2881,plain,
    ( spl4_154
  <=> m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f3063,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_154 ),
    inference(unit_resulting_resolution,[],[f2882,f111])).

fof(f2882,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_154 ),
    inference(avatar_component_clause,[],[f2881])).

fof(f3078,plain,
    ( spl4_174
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f912,f126,f3076])).

fof(f3076,plain,
    ( spl4_174
  <=> k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_tops_1(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_174])])).

fof(f912,plain,
    ( k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_tops_1(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f97,f110])).

fof(f3054,plain,
    ( ~ spl4_173
    | spl4_57 ),
    inference(avatar_split_clause,[],[f1004,f993,f3052])).

fof(f3052,plain,
    ( spl4_173
  <=> ~ r2_hidden(k2_tops_1(sK0,sK1),k3_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_173])])).

fof(f1004,plain,
    ( ~ r2_hidden(k2_tops_1(sK0,sK1),k3_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1)))
    | ~ spl4_57 ),
    inference(unit_resulting_resolution,[],[f272,f994,f119])).

fof(f272,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f200,f104])).

fof(f200,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f170,f112])).

fof(f170,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f99,f98])).

fof(f98,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',idempotence_k3_xboole_0)).

fof(f3013,plain,
    ( spl4_170
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f841,f126,f3011])).

fof(f3011,plain,
    ( spl4_170
  <=> k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f841,plain,
    ( k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f97,f109])).

fof(f3006,plain,
    ( spl4_168
    | ~ spl4_0
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f927,f861,f126,f3004])).

fof(f927,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f127,f862,f106])).

fof(f2999,plain,
    ( spl4_166
    | ~ spl4_0
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f926,f861,f126,f2997])).

fof(f926,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f127,f862,f107])).

fof(f2952,plain,
    ( spl4_164
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f867,f854,f126,f2950])).

fof(f867,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f127,f855,f106])).

fof(f2945,plain,
    ( spl4_162
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f866,f854,f126,f2943])).

fof(f866,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f127,f855,f107])).

fof(f2938,plain,
    ( spl4_160
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f865,f854,f126,f2936])).

fof(f865,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f127,f855,f108])).

fof(f2931,plain,
    ( spl4_158
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f756,f684,f126,f2929])).

fof(f756,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f127,f685,f108])).

fof(f2918,plain,
    ( spl4_156
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f1062,f984,f154,f126,f2916])).

fof(f984,plain,
    ( spl4_54
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1062,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1057,f985])).

fof(f985,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f984])).

fof(f1057,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f127,f155,f94])).

fof(f2883,plain,
    ( spl4_154
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f740,f684,f126,f2881])).

fof(f740,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f127,f685,f107])).

fof(f2851,plain,
    ( spl4_152
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f910,f140,f133,f2849])).

fof(f2849,plain,
    ( spl4_152
  <=> k1_tops_1(sK3,o_0_0_xboole_0) = k1_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f910,plain,
    ( k1_tops_1(sK3,o_0_0_xboole_0) = k1_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f202,f110])).

fof(f2844,plain,
    ( spl4_150
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f839,f140,f133,f2842])).

fof(f2842,plain,
    ( spl4_150
  <=> k2_pre_topc(sK3,o_0_0_xboole_0) = k2_pre_topc(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f839,plain,
    ( k2_pre_topc(sK3,o_0_0_xboole_0) = k2_pre_topc(sK3,k2_pre_topc(sK3,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f202,f109])).

fof(f2600,plain,
    ( spl4_148
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f909,f133,f126,f2598])).

fof(f2598,plain,
    ( spl4_148
  <=> k1_tops_1(sK0,o_0_0_xboole_0) = k1_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f909,plain,
    ( k1_tops_1(sK0,o_0_0_xboole_0) = k1_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f127,f202,f110])).

fof(f2593,plain,
    ( spl4_146
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f838,f133,f126,f2591])).

fof(f2591,plain,
    ( spl4_146
  <=> k2_pre_topc(sK0,o_0_0_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f838,plain,
    ( k2_pre_topc(sK0,o_0_0_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f127,f202,f109])).

fof(f2476,plain,
    ( spl4_144
    | ~ spl4_124 ),
    inference(avatar_split_clause,[],[f2429,f2252,f2474])).

fof(f2474,plain,
    ( spl4_144
  <=> r1_tarski(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f2252,plain,
    ( spl4_124
  <=> m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f2429,plain,
    ( r1_tarski(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3))
    | ~ spl4_124 ),
    inference(unit_resulting_resolution,[],[f2253,f111])).

fof(f2253,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_124 ),
    inference(avatar_component_clause,[],[f2252])).

fof(f2469,plain,
    ( spl4_142
    | ~ spl4_120 ),
    inference(avatar_split_clause,[],[f2364,f2182,f2467])).

fof(f2467,plain,
    ( spl4_142
  <=> r1_tarski(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f2182,plain,
    ( spl4_120
  <=> m1_subset_1(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f2364,plain,
    ( r1_tarski(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3))
    | ~ spl4_120 ),
    inference(unit_resulting_resolution,[],[f2183,f111])).

fof(f2183,plain,
    ( m1_subset_1(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_120 ),
    inference(avatar_component_clause,[],[f2182])).

fof(f2462,plain,
    ( spl4_140
    | ~ spl4_114 ),
    inference(avatar_split_clause,[],[f2296,f2130,f2460])).

fof(f2460,plain,
    ( spl4_140
  <=> r1_tarski(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f2130,plain,
    ( spl4_114
  <=> m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f2296,plain,
    ( r1_tarski(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3))
    | ~ spl4_114 ),
    inference(unit_resulting_resolution,[],[f2131,f111])).

fof(f2131,plain,
    ( m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_114 ),
    inference(avatar_component_clause,[],[f2130])).

fof(f2447,plain,
    ( spl4_138
    | ~ spl4_122 ),
    inference(avatar_split_clause,[],[f2409,f2220,f2445])).

fof(f2445,plain,
    ( spl4_138
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f2220,plain,
    ( spl4_122
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f2409,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_122 ),
    inference(unit_resulting_resolution,[],[f2221,f111])).

fof(f2221,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_122 ),
    inference(avatar_component_clause,[],[f2220])).

fof(f2399,plain,
    ( spl4_136
    | ~ spl4_118 ),
    inference(avatar_split_clause,[],[f2382,f2175,f2397])).

fof(f2397,plain,
    ( spl4_136
  <=> r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f2175,plain,
    ( spl4_118
  <=> m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f2382,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_118 ),
    inference(unit_resulting_resolution,[],[f2176,f111])).

fof(f2176,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_118 ),
    inference(avatar_component_clause,[],[f2175])).

fof(f2355,plain,
    ( spl4_134
    | ~ spl4_116 ),
    inference(avatar_split_clause,[],[f2340,f2168,f2353])).

fof(f2353,plain,
    ( spl4_134
  <=> r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f2168,plain,
    ( spl4_116
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f2340,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_116 ),
    inference(unit_resulting_resolution,[],[f2169,f111])).

fof(f2169,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_116 ),
    inference(avatar_component_clause,[],[f2168])).

fof(f2330,plain,
    ( spl4_132
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f2315,f2123,f2328])).

fof(f2328,plain,
    ( spl4_132
  <=> r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f2123,plain,
    ( spl4_112
  <=> m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f2315,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_112 ),
    inference(unit_resulting_resolution,[],[f2124,f111])).

fof(f2124,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_112 ),
    inference(avatar_component_clause,[],[f2123])).

fof(f2287,plain,
    ( spl4_130
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f1965,f1685,f2285])).

fof(f2285,plain,
    ( spl4_130
  <=> r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f1965,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl4_106 ),
    inference(unit_resulting_resolution,[],[f1686,f111])).

fof(f2280,plain,
    ( spl4_128
    | ~ spl4_102 ),
    inference(avatar_split_clause,[],[f1816,f1634,f2278])).

fof(f2278,plain,
    ( spl4_128
  <=> r1_tarski(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f1816,plain,
    ( r1_tarski(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl4_102 ),
    inference(unit_resulting_resolution,[],[f1635,f111])).

fof(f2273,plain,
    ( spl4_126
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1743,f1552,f2271])).

fof(f2271,plain,
    ( spl4_126
  <=> r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f1743,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl4_94 ),
    inference(unit_resulting_resolution,[],[f1553,f111])).

fof(f2254,plain,
    ( spl4_124
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f778,f140,f2252])).

fof(f778,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f97,f108])).

fof(f2222,plain,
    ( spl4_122
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f754,f717,f126,f2220])).

fof(f754,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f127,f718,f108])).

fof(f2184,plain,
    ( spl4_120
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f711,f140,f2182])).

fof(f711,plain,
    ( m1_subset_1(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f97,f107])).

fof(f2177,plain,
    ( spl4_118
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f721,f717,f126,f2175])).

fof(f721,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f127,f718,f106])).

fof(f2170,plain,
    ( spl4_116
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f720,f717,f126,f2168])).

fof(f720,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f127,f718,f107])).

fof(f2132,plain,
    ( spl4_114
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f652,f140,f2130])).

fof(f652,plain,
    ( m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f97,f106])).

fof(f2125,plain,
    ( spl4_112
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f689,f658,f126,f2123])).

fof(f689,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f127,f659,f107])).

fof(f1702,plain,
    ( ~ spl4_111
    | ~ spl4_2
    | spl4_57 ),
    inference(avatar_split_clause,[],[f1006,f993,f133,f1700])).

fof(f1700,plain,
    ( spl4_111
  <=> ~ r2_hidden(k2_tops_1(sK0,sK1),k3_subset_1(k1_zfmisc_1(sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_111])])).

fof(f1006,plain,
    ( ~ r2_hidden(k2_tops_1(sK0,sK1),k3_subset_1(k1_zfmisc_1(sK1),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_57 ),
    inference(unit_resulting_resolution,[],[f275,f994,f119])).

fof(f1694,plain,
    ( spl4_108
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f1670,f1566,f1692])).

fof(f1692,plain,
    ( spl4_108
  <=> r1_tarski(k2_pre_topc(sK3,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f1670,plain,
    ( r1_tarski(k2_pre_topc(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl4_98 ),
    inference(unit_resulting_resolution,[],[f1567,f111])).

fof(f1687,plain,
    ( spl4_106
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f777,f126,f1685])).

fof(f777,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f97,f108])).

fof(f1660,plain,
    ( spl4_104
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1646,f1559,f1658])).

fof(f1658,plain,
    ( spl4_104
  <=> r1_tarski(k2_tops_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f1646,plain,
    ( r1_tarski(k2_tops_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl4_96 ),
    inference(unit_resulting_resolution,[],[f1560,f111])).

fof(f1636,plain,
    ( spl4_102
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f710,f126,f1634])).

fof(f710,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f97,f107])).

fof(f1629,plain,
    ( spl4_100
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f1613,f1545,f1627])).

fof(f1627,plain,
    ( spl4_100
  <=> r1_tarski(k1_tops_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f1613,plain,
    ( r1_tarski(k1_tops_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl4_92 ),
    inference(unit_resulting_resolution,[],[f1546,f111])).

fof(f1568,plain,
    ( spl4_98
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f753,f140,f1566])).

fof(f753,plain,
    ( m1_subset_1(k2_pre_topc(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f200,f108])).

fof(f1561,plain,
    ( spl4_96
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f688,f140,f1559])).

fof(f688,plain,
    ( m1_subset_1(k2_tops_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f200,f107])).

fof(f1554,plain,
    ( spl4_94
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f651,f126,f1552])).

fof(f651,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f97,f106])).

fof(f1547,plain,
    ( spl4_92
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f630,f140,f1545])).

fof(f630,plain,
    ( m1_subset_1(k1_tops_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f200,f106])).

fof(f1434,plain,
    ( spl4_90
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f1417,f1345,f1432])).

fof(f1432,plain,
    ( spl4_90
  <=> r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f1417,plain,
    ( r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl4_84 ),
    inference(unit_resulting_resolution,[],[f1346,f111])).

fof(f1407,plain,
    ( spl4_88
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f1387,f1338,f1405])).

fof(f1405,plain,
    ( spl4_88
  <=> r1_tarski(k2_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1387,plain,
    ( r1_tarski(k2_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl4_82 ),
    inference(unit_resulting_resolution,[],[f1339,f111])).

fof(f1377,plain,
    ( spl4_86
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1361,f1331,f1375])).

fof(f1375,plain,
    ( spl4_86
  <=> r1_tarski(k1_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f1361,plain,
    ( r1_tarski(k1_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl4_80 ),
    inference(unit_resulting_resolution,[],[f1332,f111])).

fof(f1347,plain,
    ( spl4_84
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f752,f126,f1345])).

fof(f752,plain,
    ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f200,f108])).

fof(f1340,plain,
    ( spl4_82
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f687,f126,f1338])).

fof(f687,plain,
    ( m1_subset_1(k2_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f200,f107])).

fof(f1333,plain,
    ( spl4_80
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f629,f126,f1331])).

fof(f629,plain,
    ( m1_subset_1(k1_tops_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f127,f200,f106])).

fof(f1284,plain,
    ( spl4_78
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f911,f154,f126,f1282])).

fof(f911,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f127,f155,f110])).

fof(f1201,plain,
    ( ~ spl4_77
    | spl4_57 ),
    inference(avatar_split_clause,[],[f1009,f993,f1199])).

fof(f1199,plain,
    ( spl4_77
  <=> ~ r2_hidden(k2_tops_1(sK0,sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f1009,plain,
    ( ~ r2_hidden(k2_tops_1(sK0,sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(sK1))))
    | ~ spl4_57 ),
    inference(unit_resulting_resolution,[],[f97,f994,f119])).

fof(f1183,plain,
    ( spl4_74
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f1161,f1093,f1181])).

fof(f1181,plain,
    ( spl4_74
  <=> r1_tarski(k2_pre_topc(sK3,o_0_0_xboole_0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1161,plain,
    ( r1_tarski(k2_pre_topc(sK3,o_0_0_xboole_0),u1_struct_0(sK3))
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f1094,f111])).

fof(f1151,plain,
    ( spl4_72
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1137,f1086,f1149])).

fof(f1149,plain,
    ( spl4_72
  <=> r1_tarski(k2_tops_1(sK3,o_0_0_xboole_0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f1137,plain,
    ( r1_tarski(k2_tops_1(sK3,o_0_0_xboole_0),u1_struct_0(sK3))
    | ~ spl4_64 ),
    inference(unit_resulting_resolution,[],[f1087,f111])).

fof(f1127,plain,
    ( spl4_70
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f372,f154,f1125])).

fof(f1125,plain,
    ( spl4_70
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f372,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f155,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',involutiveness_k3_subset_1)).

fof(f1120,plain,
    ( spl4_68
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1104,f1079,f1118])).

fof(f1118,plain,
    ( spl4_68
  <=> r1_tarski(k1_tops_1(sK3,o_0_0_xboole_0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f1104,plain,
    ( r1_tarski(k1_tops_1(sK3,o_0_0_xboole_0),u1_struct_0(sK3))
    | ~ spl4_62 ),
    inference(unit_resulting_resolution,[],[f1080,f111])).

fof(f1095,plain,
    ( spl4_66
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f775,f140,f133,f1093])).

fof(f775,plain,
    ( m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f202,f108])).

fof(f1088,plain,
    ( spl4_64
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f708,f140,f133,f1086])).

fof(f708,plain,
    ( m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f202,f107])).

fof(f1081,plain,
    ( spl4_62
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f649,f140,f133,f1079])).

fof(f649,plain,
    ( m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f202,f106])).

fof(f1025,plain,
    ( spl4_60
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f954,f154,f147,f126,f1023])).

fof(f147,plain,
    ( spl4_6
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f954,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f127,f148,f155,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f148,plain,
    ( v5_tops_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1018,plain,
    ( ~ spl4_59
    | spl4_57 ),
    inference(avatar_split_clause,[],[f1010,f993,f1016])).

fof(f1016,plain,
    ( spl4_59
  <=> ~ r2_hidden(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f1010,plain,
    ( ~ r2_hidden(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_57 ),
    inference(unit_resulting_resolution,[],[f994,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t1_subset)).

fof(f995,plain,
    ( ~ spl4_57
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | spl4_15 ),
    inference(avatar_split_clause,[],[f958,f229,f154,f147,f126,f993])).

fof(f229,plain,
    ( spl4_15
  <=> ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f958,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f954,f232])).

fof(f232,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f230,f111])).

fof(f230,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f229])).

fof(f986,plain,
    ( spl4_54
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f956,f658,f154,f147,f126,f984])).

fof(f956,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f954,f818])).

fof(f818,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f127,f659,f109])).

fof(f977,plain,
    ( ~ spl4_53
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | spl4_15 ),
    inference(avatar_split_clause,[],[f959,f229,f154,f147,f126,f975])).

fof(f959,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f954,f230])).

fof(f946,plain,
    ( spl4_50
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f930,f861,f944])).

fof(f944,plain,
    ( spl4_50
  <=> r1_tarski(k2_pre_topc(sK0,o_0_0_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f930,plain,
    ( r1_tarski(k2_pre_topc(sK0,o_0_0_xboole_0),u1_struct_0(sK0))
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f862,f111])).

fof(f884,plain,
    ( spl4_48
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f870,f854,f882])).

fof(f882,plain,
    ( spl4_48
  <=> r1_tarski(k2_tops_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f870,plain,
    ( r1_tarski(k2_tops_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0))
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f855,f111])).

fof(f863,plain,
    ( spl4_46
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f774,f133,f126,f861])).

fof(f774,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f127,f202,f108])).

fof(f856,plain,
    ( spl4_44
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f707,f133,f126,f854])).

fof(f707,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f127,f202,f107])).

fof(f814,plain,
    ( spl4_42
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f800,f792,f812])).

fof(f812,plain,
    ( spl4_42
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f792,plain,
    ( spl4_40
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f800,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f793,f111])).

fof(f793,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f792])).

fof(f794,plain,
    ( spl4_40
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f776,f154,f126,f792])).

fof(f776,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f127,f155,f108])).

fof(f786,plain,
    ( spl4_38
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f744,f684,f784])).

fof(f784,plain,
    ( spl4_38
  <=> r1_tarski(k1_tops_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f744,plain,
    ( r1_tarski(k1_tops_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0))
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f685,f111])).

fof(f738,plain,
    ( spl4_36
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f724,f717,f736])).

fof(f736,plain,
    ( spl4_36
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f724,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f718,f111])).

fof(f719,plain,
    ( spl4_34
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f709,f154,f126,f717])).

fof(f709,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f127,f155,f107])).

fof(f686,plain,
    ( spl4_32
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f648,f133,f126,f684])).

fof(f648,plain,
    ( m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f127,f202,f106])).

fof(f678,plain,
    ( spl4_30
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f664,f658,f676])).

fof(f676,plain,
    ( spl4_30
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f664,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f659,f111])).

fof(f660,plain,
    ( spl4_28
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f650,f154,f126,f658])).

fof(f650,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f127,f155,f106])).

fof(f364,plain,
    ( spl4_26
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f357,f353,f362])).

fof(f362,plain,
    ( spl4_26
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f357,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f354,f111])).

fof(f355,plain,
    ( spl4_24
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f276,f154,f353])).

fof(f276,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f155,f104])).

fof(f338,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f315,f295,f133,f336])).

fof(f336,plain,
    ( spl4_22
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f295,plain,
    ( spl4_20
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f315,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f296,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f157,f93])).

fof(f296,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f295])).

fof(f297,plain,
    ( spl4_20
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f290,f133,f295])).

fof(f290,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f97,f288,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t2_subset)).

fof(f288,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f134,f272,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t5_subset)).

fof(f284,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f258,f246,f133,f282])).

fof(f282,plain,
    ( spl4_18
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f246,plain,
    ( spl4_16
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f258,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f247,f159])).

fof(f247,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( spl4_16
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f241,f133,f246])).

fof(f241,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f97,f238,f103])).

fof(f238,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f134,f97,f120])).

fof(f231,plain,(
    ~ spl4_15 ),
    inference(avatar_split_clause,[],[f88,f229])).

fof(f88,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f77,f76])).

fof(f76,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',t103_tops_1)).

fof(f194,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f187,f154,f192])).

fof(f192,plain,
    ( spl4_12
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f187,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f155,f111])).

fof(f169,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f157,f133,f167])).

fof(f167,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f156,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f86,f154])).

fof(f86,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f78])).

fof(f149,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f87,f147])).

fof(f87,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f78])).

fof(f142,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f121,f140])).

fof(f121,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f83])).

fof(f83,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',existence_l1_pre_topc)).

fof(f135,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f89,f133])).

fof(f89,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t103_tops_1.p',dt_o_0_0_xboole_0)).

fof(f128,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f85,f126])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).
%------------------------------------------------------------------------------
