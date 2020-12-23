%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:38 EST 2020

% Result     : Theorem 3.48s
% Output     : Refutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  340 ( 934 expanded)
%              Number of leaves         :   49 ( 331 expanded)
%              Depth                    :   32
%              Number of atoms          : 2626 (6842 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f141,f145,f150,f155,f160,f166,f218,f234,f246,f262,f272,f293,f574,f629,f656,f2026,f2034,f2055,f2182,f2234,f2249])).

fof(f2249,plain,
    ( ~ spl8_7
    | spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_38
    | spl8_46 ),
    inference(avatar_contradiction_clause,[],[f2248])).

fof(f2248,plain,
    ( $false
    | ~ spl8_7
    | spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_38
    | spl8_46 ),
    inference(subsumption_resolution,[],[f2247,f2017])).

fof(f2017,plain,
    ( l1_waybel_0(sK5(sK0),sK0)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f2016])).

fof(f2016,plain,
    ( spl8_38
  <=> l1_waybel_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f2247,plain,
    ( ~ l1_waybel_0(sK5(sK0),sK0)
    | ~ spl8_7
    | spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | spl8_46 ),
    inference(subsumption_resolution,[],[f2246,f212])).

fof(f212,plain,
    ( v7_waybel_0(sK5(sK0))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl8_15
  <=> v7_waybel_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f2246,plain,
    ( ~ v7_waybel_0(sK5(sK0))
    | ~ l1_waybel_0(sK5(sK0),sK0)
    | ~ spl8_7
    | spl8_13
    | ~ spl8_14
    | spl8_46 ),
    inference(subsumption_resolution,[],[f2245,f208])).

fof(f208,plain,
    ( v4_orders_2(sK5(sK0))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl8_14
  <=> v4_orders_2(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f2245,plain,
    ( ~ v4_orders_2(sK5(sK0))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ l1_waybel_0(sK5(sK0),sK0)
    | ~ spl8_7
    | spl8_13
    | spl8_46 ),
    inference(subsumption_resolution,[],[f2243,f204])).

fof(f204,plain,
    ( ~ v2_struct_0(sK5(sK0))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl8_13
  <=> v2_struct_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f2243,plain,
    ( v2_struct_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ l1_waybel_0(sK5(sK0),sK0)
    | ~ spl8_7
    | spl8_46 ),
    inference(resolution,[],[f2233,f140])).

fof(f140,plain,
    ( ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_7
  <=> ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f2233,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | spl8_46 ),
    inference(avatar_component_clause,[],[f2231])).

fof(f2231,plain,
    ( spl8_46
  <=> v3_yellow_6(sK2(sK5(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f2234,plain,
    ( ~ spl8_46
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_39
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f2229,f2179,f2020,f286,f259,f215,f157,f152,f147,f2231])).

fof(f147,plain,
    ( spl8_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f152,plain,
    ( spl8_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f157,plain,
    ( spl8_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f215,plain,
    ( spl8_16
  <=> v2_struct_0(sK2(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f259,plain,
    ( spl8_17
  <=> v4_orders_2(sK2(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f286,plain,
    ( spl8_18
  <=> v7_waybel_0(sK2(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f2020,plain,
    ( spl8_39
  <=> l1_waybel_0(sK2(sK5(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f2179,plain,
    ( spl8_45
  <=> k1_xboole_0 = k10_yellow_6(sK0,sK2(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f2229,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_39
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2228,f159])).

fof(f159,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f2228,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | v2_struct_0(sK0)
    | ~ spl8_9
    | ~ spl8_10
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_39
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2227,f154])).

fof(f154,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f2227,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_9
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_39
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2226,f149])).

fof(f149,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f2226,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_39
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2225,f217])).

fof(f217,plain,
    ( ~ v2_struct_0(sK2(sK5(sK0)))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f215])).

fof(f2225,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | v2_struct_0(sK2(sK5(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_39
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2224,f261])).

fof(f261,plain,
    ( v4_orders_2(sK2(sK5(sK0)))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f259])).

fof(f2224,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | ~ v4_orders_2(sK2(sK5(sK0)))
    | v2_struct_0(sK2(sK5(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_18
    | ~ spl8_39
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2223,f288])).

fof(f288,plain,
    ( v7_waybel_0(sK2(sK5(sK0)))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f286])).

fof(f2223,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK5(sK0)))
    | ~ v4_orders_2(sK2(sK5(sK0)))
    | v2_struct_0(sK2(sK5(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_39
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2222,f2021])).

fof(f2021,plain,
    ( l1_waybel_0(sK2(sK5(sK0)),sK0)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f2020])).

fof(f2222,plain,
    ( ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK5(sK0)))
    | ~ v4_orders_2(sK2(sK5(sK0)))
    | v2_struct_0(sK2(sK5(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_45 ),
    inference(trivial_inequality_removal,[],[f2209])).

fof(f2209,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK2(sK5(sK0)),sK0)
    | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK5(sK0)))
    | ~ v4_orders_2(sK2(sK5(sK0)))
    | v2_struct_0(sK2(sK5(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_45 ),
    inference(superposition,[],[f75,f2181])).

fof(f2181,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK5(sK0)))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f2179])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_yellow_6(X0,X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k1_xboole_0 = k10_yellow_6(X0,X1) )
            & ( k1_xboole_0 != k10_yellow_6(X0,X1)
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f2182,plain,
    ( spl8_45
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f2143,f2024,f2179])).

fof(f2024,plain,
    ( spl8_40
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f2143,plain,
    ( k1_xboole_0 = k10_yellow_6(sK0,sK2(sK5(sK0)))
    | ~ spl8_40 ),
    inference(resolution,[],[f2111,f173])).

fof(f173,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f99,f167])).

fof(f167,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f102,f100])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2111,plain,
    ( ! [X0] : r1_tarski(k10_yellow_6(sK0,sK2(sK5(sK0))),X0)
    | ~ spl8_40 ),
    inference(resolution,[],[f2025,f108])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2025,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1) )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f2024])).

fof(f2055,plain,
    ( ~ spl8_8
    | spl8_11
    | ~ spl8_12
    | spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_38
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f2054])).

fof(f2054,plain,
    ( $false
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12
    | spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_38
    | spl8_39 ),
    inference(subsumption_resolution,[],[f2053,f204])).

fof(f2053,plain,
    ( v2_struct_0(sK5(sK0))
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_38
    | spl8_39 ),
    inference(subsumption_resolution,[],[f2052,f208])).

fof(f2052,plain,
    ( ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12
    | ~ spl8_15
    | ~ spl8_38
    | spl8_39 ),
    inference(subsumption_resolution,[],[f2051,f212])).

fof(f2051,plain,
    ( ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12
    | ~ spl8_38
    | spl8_39 ),
    inference(subsumption_resolution,[],[f2049,f2017])).

fof(f2049,plain,
    ( ~ l1_waybel_0(sK5(sK0),sK0)
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12
    | spl8_39 ),
    inference(resolution,[],[f2022,f238])).

fof(f238,plain,
    ( ! [X0] :
        ( l1_waybel_0(sK2(X0),sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f237,f159])).

fof(f237,plain,
    ( ! [X0] :
        ( l1_waybel_0(sK2(X0),sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f236,f165])).

fof(f165,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f236,plain,
    ( ! [X0] :
        ( l1_waybel_0(sK2(X0),sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ! [X0] :
        ( l1_waybel_0(sK2(X0),sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f80,f144])).

fof(f144,plain,
    ( ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_8
  <=> ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f2022,plain,
    ( ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
    | spl8_39 ),
    inference(avatar_component_clause,[],[f2020])).

fof(f2034,plain,
    ( spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_38 ),
    inference(avatar_contradiction_clause,[],[f2033])).

fof(f2033,plain,
    ( $false
    | spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_38 ),
    inference(subsumption_resolution,[],[f2032,f159])).

fof(f2032,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_38 ),
    inference(subsumption_resolution,[],[f2031,f154])).

fof(f2031,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_9
    | spl8_38 ),
    inference(subsumption_resolution,[],[f2030,f149])).

fof(f2030,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_38 ),
    inference(subsumption_resolution,[],[f2028,f113])).

fof(f113,plain,
    ( ~ v1_compts_1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2028,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_38 ),
    inference(resolution,[],[f2018,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_waybel_0(sK5(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK5(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(sK5(X0),k6_yellow_6(X0))
            & l1_waybel_0(sK5(X0),X0)
            & v7_waybel_0(sK5(X0))
            & v4_orders_2(sK5(X0))
            & ~ v2_struct_0(sK5(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK6(X0,X3))
                & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f54,f56,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK5(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK5(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK5(X0),X0)
        & v7_waybel_0(sK5(X0))
        & v4_orders_2(sK5(X0))
        & ~ v2_struct_0(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK6(X0,X3))
        & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r2_hidden(X1,k6_yellow_6(X0))
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).

fof(f2018,plain,
    ( ~ l1_waybel_0(sK5(sK0),sK0)
    | spl8_38 ),
    inference(avatar_component_clause,[],[f2016])).

fof(f2026,plain,
    ( ~ spl8_38
    | ~ spl8_39
    | spl8_40
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f2014,f286,f259,f215,f211,f207,f203,f157,f152,f147,f143,f111,f2024,f2020,f2016])).

fof(f2014,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f2013,f212])).

fof(f2013,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_13
    | ~ spl8_14
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f2012,f208])).

fof(f2012,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_13
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f2011,f204])).

fof(f2011,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | v2_struct_0(sK5(sK0))
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f2010,f113])).

fof(f2010,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | v1_compts_1(sK0)
        | v2_struct_0(sK5(sK0))
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_16
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f2009,f288])).

fof(f2009,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ v7_waybel_0(sK2(sK5(sK0)))
        | v1_compts_1(sK0)
        | v2_struct_0(sK5(sK0))
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_16
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f2008,f159])).

fof(f2008,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ v7_waybel_0(sK2(sK5(sK0)))
        | v1_compts_1(sK0)
        | v2_struct_0(sK5(sK0))
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_16
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f2007,f154])).

fof(f2007,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ v7_waybel_0(sK2(sK5(sK0)))
        | v1_compts_1(sK0)
        | v2_struct_0(sK5(sK0))
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | ~ spl8_8
    | ~ spl8_9
    | spl8_16
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f2006,f149])).

fof(f2006,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ v7_waybel_0(sK2(sK5(sK0)))
        | v1_compts_1(sK0)
        | v2_struct_0(sK5(sK0))
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | ~ spl8_8
    | spl8_16
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f2005,f217])).

fof(f2005,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2(sK5(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ v7_waybel_0(sK2(sK5(sK0)))
        | v1_compts_1(sK0)
        | v2_struct_0(sK5(sK0))
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f2002,f261])).

fof(f2002,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK2(sK5(sK0)))
        | v2_struct_0(sK2(sK5(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0))))
        | r1_tarski(X0,X1)
        | ~ l1_waybel_0(sK2(sK5(sK0)),sK0)
        | ~ v7_waybel_0(sK2(sK5(sK0)))
        | v1_compts_1(sK0)
        | v2_struct_0(sK5(sK0))
        | ~ v4_orders_2(sK5(sK0))
        | ~ v7_waybel_0(sK5(sK0))
        | ~ l1_waybel_0(sK5(sK0),sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f1004,f144])).

fof(f1004,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m2_yellow_6(X0,X1,sK5(X1))
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | r1_tarski(X2,X3)
      | ~ l1_waybel_0(X0,X1)
      | ~ v7_waybel_0(X0)
      | v1_compts_1(X1) ) ),
    inference(subsumption_resolution,[],[f1003,f391])).

fof(f391,plain,(
    ! [X6,X4,X5,X3] :
      ( m1_subset_1(sK7(X5,X6),u1_struct_0(X4))
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ v7_waybel_0(X3)
      | ~ l1_waybel_0(X3,X4)
      | ~ r1_tarski(X5,k10_yellow_6(X4,X3))
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f247,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f105,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X1,X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f84,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f1003,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | r1_tarski(X2,X3)
      | ~ l1_waybel_0(X0,X1)
      | ~ m2_yellow_6(X0,X1,sK5(X1))
      | v1_compts_1(X1)
      | ~ m1_subset_1(sK7(X2,X3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1002,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK5(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1002,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | r1_tarski(X2,X3)
      | ~ l1_waybel_0(X0,X1)
      | ~ m2_yellow_6(X0,X1,sK5(X1))
      | v2_struct_0(sK5(X1))
      | v1_compts_1(X1)
      | ~ m1_subset_1(sK7(X2,X3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1001,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v4_orders_2(sK5(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1001,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | r1_tarski(X2,X3)
      | ~ l1_waybel_0(X0,X1)
      | ~ m2_yellow_6(X0,X1,sK5(X1))
      | ~ v4_orders_2(sK5(X1))
      | v2_struct_0(sK5(X1))
      | v1_compts_1(X1)
      | ~ m1_subset_1(sK7(X2,X3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1000,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v7_waybel_0(sK5(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1000,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | r1_tarski(X2,X3)
      | ~ l1_waybel_0(X0,X1)
      | ~ m2_yellow_6(X0,X1,sK5(X1))
      | ~ v7_waybel_0(sK5(X1))
      | ~ v4_orders_2(sK5(X1))
      | v2_struct_0(sK5(X1))
      | v1_compts_1(X1)
      | ~ m1_subset_1(sK7(X2,X3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f999,f93])).

fof(f999,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | r1_tarski(X2,X3)
      | ~ l1_waybel_0(X0,X1)
      | ~ m2_yellow_6(X0,X1,sK5(X1))
      | ~ l1_waybel_0(sK5(X1),X1)
      | ~ v7_waybel_0(sK5(X1))
      | ~ v4_orders_2(sK5(X1))
      | v2_struct_0(sK5(X1))
      | v1_compts_1(X1)
      | ~ m1_subset_1(sK7(X2,X3),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f992])).

fof(f992,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | r1_tarski(X2,X3)
      | ~ l1_waybel_0(X0,X1)
      | ~ m2_yellow_6(X0,X1,sK5(X1))
      | ~ l1_waybel_0(sK5(X1),X1)
      | ~ v7_waybel_0(sK5(X1))
      | ~ v4_orders_2(sK5(X1))
      | v2_struct_0(sK5(X1))
      | v1_compts_1(X1)
      | ~ m1_subset_1(sK7(X2,X3),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f772,f95])).

fof(f95,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK5(X0),X2)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f772,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( r3_waybel_9(X8,X11,sK7(X9,X10))
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ r1_tarski(X9,k10_yellow_6(X8,X7))
      | r1_tarski(X9,X10)
      | ~ l1_waybel_0(X7,X8)
      | ~ m2_yellow_6(X7,X8,X11)
      | ~ l1_waybel_0(X11,X8)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f764,f391])).

fof(f764,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( ~ l1_waybel_0(X7,X8)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ r1_tarski(X9,k10_yellow_6(X8,X7))
      | r1_tarski(X9,X10)
      | r3_waybel_9(X8,X11,sK7(X9,X10))
      | ~ m1_subset_1(sK7(X9,X10),u1_struct_0(X8))
      | ~ m2_yellow_6(X7,X8,X11)
      | ~ l1_waybel_0(X11,X8)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11) ) ),
    inference(duplicate_literal_removal,[],[f761])).

fof(f761,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( ~ l1_waybel_0(X7,X8)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ r1_tarski(X9,k10_yellow_6(X8,X7))
      | r1_tarski(X9,X10)
      | r3_waybel_9(X8,X11,sK7(X9,X10))
      | ~ m1_subset_1(sK7(X9,X10),u1_struct_0(X8))
      | ~ m2_yellow_6(X7,X8,X11)
      | ~ l1_waybel_0(X11,X8)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(resolution,[],[f758,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_waybel_9(X0,X2,X3)
      | r3_waybel_9(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f758,plain,(
    ! [X6,X4,X5,X3] :
      ( r3_waybel_9(X3,X4,sK7(X5,X6))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r1_tarski(X5,k10_yellow_6(X3,X4))
      | r1_tarski(X5,X6) ) ),
    inference(subsumption_resolution,[],[f276,f391])).

fof(f276,plain,(
    ! [X6,X4,X5,X3] :
      ( r3_waybel_9(X3,X4,sK7(X5,X6))
      | ~ m1_subset_1(sK7(X5,X6),u1_struct_0(X3))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r1_tarski(X5,k10_yellow_6(X3,X4))
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f85,f176])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f656,plain,(
    ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f651,f167])).

fof(f651,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK0,sK1))
    | ~ spl8_28 ),
    inference(resolution,[],[f628,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f628,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl8_28
  <=> r2_hidden(sK4(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f629,plain,
    ( spl8_28
    | ~ spl8_25
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(avatar_split_clause,[],[f624,f157,f152,f147,f134,f129,f124,f119,f115,f111,f514,f626])).

fof(f514,plain,
    ( spl8_25
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f115,plain,
    ( spl8_2
  <=> ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f119,plain,
    ( spl8_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f124,plain,
    ( spl8_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f129,plain,
    ( spl8_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f134,plain,
    ( spl8_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f624,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f623,f159])).

fof(f623,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f622,f154])).

fof(f622,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f621,f149])).

fof(f621,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f620,f112])).

fof(f112,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f620,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f619,f136])).

fof(f136,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f619,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f618,f131])).

fof(f131,plain,
    ( v4_orders_2(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f618,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f617,f126])).

fof(f126,plain,
    ( v7_waybel_0(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f617,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f612,f121])).

fof(f121,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f612,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(resolution,[],[f611,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK4(X0,X1))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).

fof(f611,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f610,f159])).

fof(f610,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f609,f154])).

fof(f609,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f608,f149])).

fof(f608,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f607,f136])).

fof(f607,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f606,f131])).

fof(f606,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f605,f126])).

fof(f605,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f604,f121])).

fof(f604,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(duplicate_literal_removal,[],[f603])).

fof(f603,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(resolution,[],[f578,f350])).

fof(f350,plain,
    ( ! [X12] :
        ( ~ v3_yellow_6(sK3(sK0,sK1,X12),sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X12) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f349,f159])).

fof(f349,plain,
    ( ! [X12] :
        ( ~ r3_waybel_9(sK0,sK1,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v3_yellow_6(sK3(sK0,sK1,X12),sK0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f348,f154])).

fof(f348,plain,
    ( ! [X12] :
        ( ~ r3_waybel_9(sK0,sK1,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_yellow_6(sK3(sK0,sK1,X12),sK0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f347,f149])).

fof(f347,plain,
    ( ! [X12] :
        ( ~ r3_waybel_9(sK0,sK1,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_yellow_6(sK3(sK0,sK1,X12),sK0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f346,f136])).

fof(f346,plain,
    ( ! [X12] :
        ( ~ r3_waybel_9(sK0,sK1,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_yellow_6(sK3(sK0,sK1,X12),sK0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f345,f131])).

fof(f345,plain,
    ( ! [X12] :
        ( ~ r3_waybel_9(sK0,sK1,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_yellow_6(sK3(sK0,sK1,X12),sK0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f344,f126])).

fof(f344,plain,
    ( ! [X12] :
        ( ~ r3_waybel_9(sK0,sK1,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_yellow_6(sK3(sK0,sK1,X12),sK0) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f335,f121])).

fof(f335,plain,
    ( ! [X12] :
        ( ~ r3_waybel_9(sK0,sK1,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_yellow_6(sK3(sK0,sK1,X12),sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f82,f116])).

fof(f116,plain,
    ( ! [X2] :
        ( ~ m2_yellow_6(X2,sK0,sK1)
        | ~ v3_yellow_6(X2,sK0) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK3(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
                & m2_yellow_6(sK3(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
        & m2_yellow_6(sK3(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f578,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK3(X0,X1,X2),X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(X2,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f577,f343])).

fof(f343,plain,(
    ! [X10,X11,X9] :
      ( ~ v2_struct_0(sK3(X9,X10,X11))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ l1_waybel_0(X10,X9)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ r3_waybel_9(X9,X10,X11) ) ),
    inference(subsumption_resolution,[],[f336,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f336,plain,(
    ! [X10,X11,X9] :
      ( ~ r3_waybel_9(X9,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ l1_waybel_0(X10,X9)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ v2_struct_0(sK3(X9,X10,X11))
      | ~ l1_struct_0(X9) ) ),
    inference(duplicate_literal_removal,[],[f334])).

fof(f334,plain,(
    ! [X10,X11,X9] :
      ( ~ r3_waybel_9(X9,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ l1_waybel_0(X10,X9)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ v2_struct_0(sK3(X9,X10,X11))
      | ~ l1_waybel_0(X10,X9)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_struct_0(X9)
      | v2_struct_0(X9) ) ),
    inference(resolution,[],[f82,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f577,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_yellow_6(sK3(X0,X1,X2),X0)
      | v2_struct_0(sK3(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f576,f342])).

fof(f342,plain,(
    ! [X6,X8,X7] :
      ( v4_orders_2(sK3(X6,X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ r3_waybel_9(X6,X7,X8) ) ),
    inference(subsumption_resolution,[],[f337,f96])).

fof(f337,plain,(
    ! [X6,X8,X7] :
      ( ~ r3_waybel_9(X6,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | v4_orders_2(sK3(X6,X7,X8))
      | ~ l1_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,(
    ! [X6,X8,X7] :
      ( ~ r3_waybel_9(X6,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | v4_orders_2(sK3(X6,X7,X8))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_struct_0(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f82,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f576,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_yellow_6(sK3(X0,X1,X2),X0)
      | ~ v4_orders_2(sK3(X0,X1,X2))
      | v2_struct_0(sK3(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f575,f341])).

fof(f341,plain,(
    ! [X4,X5,X3] :
      ( v7_waybel_0(sK3(X3,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r3_waybel_9(X3,X4,X5) ) ),
    inference(subsumption_resolution,[],[f338,f96])).

fof(f338,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_waybel_9(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | v7_waybel_0(sK3(X3,X4,X5))
      | ~ l1_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_waybel_9(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | v7_waybel_0(sK3(X3,X4,X5))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f82,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f575,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_yellow_6(sK3(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK3(X0,X1,X2))
      | ~ v4_orders_2(sK3(X0,X1,X2))
      | v2_struct_0(sK3(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f362,f340])).

fof(f340,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f339,f96])).

fof(f339,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_waybel_0(sK3(X0,X1,X2),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_waybel_0(sK3(X0,X1,X2),X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f82,f80])).

fof(f362,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_yellow_6(sK3(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK3(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK3(X0,X1,X2))
      | ~ v4_orders_2(sK3(X0,X1,X2))
      | v2_struct_0(sK3(X0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_yellow_6(sK3(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK3(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK3(X0,X1,X2))
      | ~ v4_orders_2(sK3(X0,X1,X2))
      | v2_struct_0(sK3(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f83,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_yellow_6(X0,X1)
      | v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f574,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_25 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_25 ),
    inference(subsumption_resolution,[],[f572,f159])).

fof(f572,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | spl8_25 ),
    inference(subsumption_resolution,[],[f571,f154])).

fof(f571,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | spl8_25 ),
    inference(subsumption_resolution,[],[f570,f149])).

fof(f570,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | spl8_25 ),
    inference(subsumption_resolution,[],[f569,f112])).

fof(f569,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | spl8_25 ),
    inference(subsumption_resolution,[],[f568,f136])).

fof(f568,plain,
    ( v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_25 ),
    inference(subsumption_resolution,[],[f567,f131])).

fof(f567,plain,
    ( ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_25 ),
    inference(subsumption_resolution,[],[f566,f126])).

fof(f566,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | spl8_25 ),
    inference(subsumption_resolution,[],[f564,f121])).

fof(f564,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_25 ),
    inference(resolution,[],[f516,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f516,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | spl8_25 ),
    inference(avatar_component_clause,[],[f514])).

fof(f293,plain,
    ( spl8_1
    | spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | spl8_18
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f292,f163,f157,f152,f147,f143,f286,f211,f207,f203,f111])).

fof(f292,plain,
    ( v7_waybel_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | v1_compts_1(sK0)
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f291,f159])).

fof(f291,plain,
    ( v7_waybel_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | v1_compts_1(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f290,f154])).

fof(f290,plain,
    ( v7_waybel_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_8
    | ~ spl8_9
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f280,f149])).

fof(f280,plain,
    ( v7_waybel_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f226,f93])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | v7_waybel_0(sK2(X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f225,f159])).

fof(f225,plain,
    ( ! [X0] :
        ( v7_waybel_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f224,f165])).

fof(f224,plain,
    ( ! [X0] :
        ( v7_waybel_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( ! [X0] :
        ( v7_waybel_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f79,f144])).

fof(f272,plain,
    ( spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f270,f159])).

fof(f270,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f269,f154])).

fof(f269,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f268,f149])).

fof(f268,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f266,f113])).

fof(f266,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_13 ),
    inference(resolution,[],[f205,f90])).

fof(f205,plain,
    ( v2_struct_0(sK5(sK0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f262,plain,
    ( spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | spl8_17
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f257,f163,f157,f152,f147,f143,f111,f259,f211,f207,f203])).

fof(f257,plain,
    ( v4_orders_2(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f256,f159])).

fof(f256,plain,
    ( v4_orders_2(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f255,f154])).

fof(f255,plain,
    ( v4_orders_2(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f254,f149])).

fof(f254,plain,
    ( v4_orders_2(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f253,f113])).

fof(f253,plain,
    ( v4_orders_2(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f222,f93])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | v4_orders_2(sK2(X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f221,f159])).

fof(f221,plain,
    ( ! [X0] :
        ( v4_orders_2(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f220,f165])).

fof(f220,plain,
    ( ! [X0] :
        ( v4_orders_2(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( ! [X0] :
        ( v4_orders_2(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f78,f144])).

fof(f246,plain,
    ( spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_15 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_15 ),
    inference(subsumption_resolution,[],[f244,f159])).

fof(f244,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_15 ),
    inference(subsumption_resolution,[],[f243,f154])).

fof(f243,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_9
    | spl8_15 ),
    inference(subsumption_resolution,[],[f242,f149])).

fof(f242,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_15 ),
    inference(subsumption_resolution,[],[f240,f113])).

fof(f240,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_15 ),
    inference(resolution,[],[f213,f92])).

fof(f213,plain,
    ( ~ v7_waybel_0(sK5(sK0))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f234,plain,
    ( spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | spl8_14 ),
    inference(subsumption_resolution,[],[f232,f159])).

fof(f232,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_9
    | ~ spl8_10
    | spl8_14 ),
    inference(subsumption_resolution,[],[f231,f154])).

fof(f231,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_9
    | spl8_14 ),
    inference(subsumption_resolution,[],[f230,f149])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_14 ),
    inference(subsumption_resolution,[],[f228,f113])).

fof(f228,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_14 ),
    inference(resolution,[],[f209,f91])).

fof(f209,plain,
    ( ~ v4_orders_2(sK5(sK0))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f218,plain,
    ( spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f201,f163,f157,f152,f147,f143,f111,f215,f211,f207,f203])).

fof(f201,plain,
    ( ~ v2_struct_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f200,f159])).

fof(f200,plain,
    ( ~ v2_struct_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f199,f154])).

fof(f199,plain,
    ( ~ v2_struct_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f198,f149])).

fof(f198,plain,
    ( ~ v2_struct_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f197,f113])).

fof(f197,plain,
    ( ~ v2_struct_0(sK2(sK5(sK0)))
    | ~ v7_waybel_0(sK5(sK0))
    | ~ v4_orders_2(sK5(sK0))
    | v2_struct_0(sK5(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f196,f93])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ v2_struct_0(sK2(X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl8_8
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f195,f159])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f194,f165])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f77,f144])).

fof(f166,plain,
    ( spl8_12
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f161,f147,f163])).

fof(f161,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_9 ),
    inference(resolution,[],[f96,f149])).

fof(f160,plain,(
    ~ spl8_11 ),
    inference(avatar_split_clause,[],[f65,f157])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,sK1) )
        & l1_waybel_0(sK1,sK0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) )
      | ~ v1_compts_1(sK0) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK2(X3),sK0)
            & m2_yellow_6(sK2(X3),sK0,X3) )
          | ~ l1_waybel_0(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ v3_yellow_6(X2,X0)
                  | ~ m2_yellow_6(X2,X0,X1) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v3_yellow_6(X4,X0)
                  & m2_yellow_6(X4,X0,X3) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,sK0)
                | ~ m2_yellow_6(X2,sK0,X1) )
            & l1_waybel_0(X1,sK0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK0)
                & m2_yellow_6(X4,sK0,X3) )
            | ~ l1_waybel_0(X3,sK0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ v3_yellow_6(X2,sK0)
          | ~ m2_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,X0)
                & m2_yellow_6(X4,X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( v3_yellow_6(X2,X0)
                  & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).

fof(f155,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f66,f152])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f150,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f67,f147])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f145,plain,
    ( spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f68,f143,f111])).

fof(f68,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f141,plain,
    ( spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f69,f139,f111])).

fof(f69,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,
    ( ~ spl8_1
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f70,f134,f111])).

fof(f70,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f132,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f71,f129,f111])).

fof(f71,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f127,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f72,f124,f111])).

fof(f72,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f122,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f73,f119,f111])).

fof(f73,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f74,f115,f111])).

fof(f74,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK0)
      | ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 09:48:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.51  % (4140)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.52  % (4149)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.52  % (4149)Refutation not found, incomplete strategy% (4149)------------------------------
% 0.23/0.52  % (4149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (4164)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.53  % (4153)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (4156)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.53  % (4149)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (4149)Memory used [KB]: 10874
% 0.23/0.53  % (4149)Time elapsed: 0.086 s
% 0.23/0.53  % (4149)------------------------------
% 0.23/0.53  % (4149)------------------------------
% 0.23/0.53  % (4169)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.53  % (4144)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (4145)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (4144)Refutation not found, incomplete strategy% (4144)------------------------------
% 0.23/0.54  % (4144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (4144)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (4144)Memory used [KB]: 6268
% 0.23/0.54  % (4144)Time elapsed: 0.106 s
% 0.23/0.54  % (4144)------------------------------
% 0.23/0.54  % (4144)------------------------------
% 0.23/0.54  % (4148)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.54  % (4162)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.55  % (4166)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.55  % (4151)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (4165)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.55  % (4141)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.55  % (4154)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.55  % (4168)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.55  % (4142)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.56  % (4143)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.56  % (4147)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.56  % (4161)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.56  % (4146)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.56  % (4158)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.56  % (4160)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.57  % (4162)Refutation not found, incomplete strategy% (4162)------------------------------
% 0.23/0.57  % (4162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (4162)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (4162)Memory used [KB]: 10874
% 0.23/0.57  % (4162)Time elapsed: 0.086 s
% 0.23/0.57  % (4162)------------------------------
% 0.23/0.57  % (4162)------------------------------
% 0.23/0.57  % (4167)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.57  % (4157)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.57  % (4163)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.57  % (4151)Refutation not found, incomplete strategy% (4151)------------------------------
% 1.51/0.57  % (4151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (4151)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (4151)Memory used [KB]: 10746
% 1.51/0.57  % (4151)Time elapsed: 0.154 s
% 1.51/0.57  % (4151)------------------------------
% 1.51/0.57  % (4151)------------------------------
% 1.51/0.57  % (4159)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.58  % (4152)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.58  % (4150)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.58  % (4150)Refutation not found, incomplete strategy% (4150)------------------------------
% 1.51/0.58  % (4150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (4150)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (4150)Memory used [KB]: 10746
% 1.51/0.58  % (4150)Time elapsed: 0.148 s
% 1.51/0.58  % (4150)------------------------------
% 1.51/0.58  % (4150)------------------------------
% 1.51/0.58  % (4155)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.99/0.67  % (4171)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.99/0.68  % (4172)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.99/0.68  % (4170)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.99/0.71  % (4170)Refutation not found, incomplete strategy% (4170)------------------------------
% 1.99/0.71  % (4170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.71  % (4170)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.71  
% 1.99/0.71  % (4170)Memory used [KB]: 6268
% 1.99/0.71  % (4170)Time elapsed: 0.120 s
% 1.99/0.71  % (4170)------------------------------
% 1.99/0.71  % (4170)------------------------------
% 2.46/0.71  % (4174)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.89/0.78  % (4175)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.89/0.84  % (4145)Time limit reached!
% 2.89/0.84  % (4145)------------------------------
% 2.89/0.84  % (4145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.84  % (4145)Termination reason: Time limit
% 2.89/0.84  
% 2.89/0.84  % (4145)Memory used [KB]: 7547
% 2.89/0.84  % (4145)Time elapsed: 0.415 s
% 2.89/0.84  % (4145)------------------------------
% 2.89/0.84  % (4145)------------------------------
% 3.48/0.87  % (4176)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.48/0.87  % (4172)Refutation found. Thanks to Tanya!
% 3.48/0.87  % SZS status Theorem for theBenchmark
% 3.48/0.87  % SZS output start Proof for theBenchmark
% 3.48/0.87  fof(f2250,plain,(
% 3.48/0.87    $false),
% 3.48/0.87    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f141,f145,f150,f155,f160,f166,f218,f234,f246,f262,f272,f293,f574,f629,f656,f2026,f2034,f2055,f2182,f2234,f2249])).
% 3.48/0.87  fof(f2249,plain,(
% 3.48/0.87    ~spl8_7 | spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_38 | spl8_46),
% 3.48/0.87    inference(avatar_contradiction_clause,[],[f2248])).
% 3.48/0.87  fof(f2248,plain,(
% 3.48/0.87    $false | (~spl8_7 | spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_38 | spl8_46)),
% 3.48/0.87    inference(subsumption_resolution,[],[f2247,f2017])).
% 3.48/0.87  fof(f2017,plain,(
% 3.48/0.87    l1_waybel_0(sK5(sK0),sK0) | ~spl8_38),
% 3.48/0.87    inference(avatar_component_clause,[],[f2016])).
% 3.48/0.88  fof(f2016,plain,(
% 3.48/0.88    spl8_38 <=> l1_waybel_0(sK5(sK0),sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 3.48/0.88  fof(f2247,plain,(
% 3.48/0.88    ~l1_waybel_0(sK5(sK0),sK0) | (~spl8_7 | spl8_13 | ~spl8_14 | ~spl8_15 | spl8_46)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2246,f212])).
% 3.48/0.88  fof(f212,plain,(
% 3.48/0.88    v7_waybel_0(sK5(sK0)) | ~spl8_15),
% 3.48/0.88    inference(avatar_component_clause,[],[f211])).
% 3.48/0.88  fof(f211,plain,(
% 3.48/0.88    spl8_15 <=> v7_waybel_0(sK5(sK0))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 3.48/0.88  fof(f2246,plain,(
% 3.48/0.88    ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0) | (~spl8_7 | spl8_13 | ~spl8_14 | spl8_46)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2245,f208])).
% 3.48/0.88  fof(f208,plain,(
% 3.48/0.88    v4_orders_2(sK5(sK0)) | ~spl8_14),
% 3.48/0.88    inference(avatar_component_clause,[],[f207])).
% 3.48/0.88  fof(f207,plain,(
% 3.48/0.88    spl8_14 <=> v4_orders_2(sK5(sK0))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 3.48/0.88  fof(f2245,plain,(
% 3.48/0.88    ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0) | (~spl8_7 | spl8_13 | spl8_46)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2243,f204])).
% 3.48/0.88  fof(f204,plain,(
% 3.48/0.88    ~v2_struct_0(sK5(sK0)) | spl8_13),
% 3.48/0.88    inference(avatar_component_clause,[],[f203])).
% 3.48/0.88  fof(f203,plain,(
% 3.48/0.88    spl8_13 <=> v2_struct_0(sK5(sK0))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 3.48/0.88  fof(f2243,plain,(
% 3.48/0.88    v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0) | (~spl8_7 | spl8_46)),
% 3.48/0.88    inference(resolution,[],[f2233,f140])).
% 3.48/0.88  fof(f140,plain,(
% 3.48/0.88    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl8_7),
% 3.48/0.88    inference(avatar_component_clause,[],[f139])).
% 3.48/0.88  fof(f139,plain,(
% 3.48/0.88    spl8_7 <=> ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 3.48/0.88  fof(f2233,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | spl8_46),
% 3.48/0.88    inference(avatar_component_clause,[],[f2231])).
% 3.48/0.88  fof(f2231,plain,(
% 3.48/0.88    spl8_46 <=> v3_yellow_6(sK2(sK5(sK0)),sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 3.48/0.88  fof(f2234,plain,(
% 3.48/0.88    ~spl8_46 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_16 | ~spl8_17 | ~spl8_18 | ~spl8_39 | ~spl8_45),
% 3.48/0.88    inference(avatar_split_clause,[],[f2229,f2179,f2020,f286,f259,f215,f157,f152,f147,f2231])).
% 3.48/0.88  fof(f147,plain,(
% 3.48/0.88    spl8_9 <=> l1_pre_topc(sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 3.48/0.88  fof(f152,plain,(
% 3.48/0.88    spl8_10 <=> v2_pre_topc(sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 3.48/0.88  fof(f157,plain,(
% 3.48/0.88    spl8_11 <=> v2_struct_0(sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 3.48/0.88  fof(f215,plain,(
% 3.48/0.88    spl8_16 <=> v2_struct_0(sK2(sK5(sK0)))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 3.48/0.88  fof(f259,plain,(
% 3.48/0.88    spl8_17 <=> v4_orders_2(sK2(sK5(sK0)))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 3.48/0.88  fof(f286,plain,(
% 3.48/0.88    spl8_18 <=> v7_waybel_0(sK2(sK5(sK0)))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 3.48/0.88  fof(f2020,plain,(
% 3.48/0.88    spl8_39 <=> l1_waybel_0(sK2(sK5(sK0)),sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 3.48/0.88  fof(f2179,plain,(
% 3.48/0.88    spl8_45 <=> k1_xboole_0 = k10_yellow_6(sK0,sK2(sK5(sK0)))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 3.48/0.88  fof(f2229,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | (~spl8_9 | ~spl8_10 | spl8_11 | spl8_16 | ~spl8_17 | ~spl8_18 | ~spl8_39 | ~spl8_45)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2228,f159])).
% 3.48/0.88  fof(f159,plain,(
% 3.48/0.88    ~v2_struct_0(sK0) | spl8_11),
% 3.48/0.88    inference(avatar_component_clause,[],[f157])).
% 3.48/0.88  fof(f2228,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | v2_struct_0(sK0) | (~spl8_9 | ~spl8_10 | spl8_16 | ~spl8_17 | ~spl8_18 | ~spl8_39 | ~spl8_45)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2227,f154])).
% 3.48/0.88  fof(f154,plain,(
% 3.48/0.88    v2_pre_topc(sK0) | ~spl8_10),
% 3.48/0.88    inference(avatar_component_clause,[],[f152])).
% 3.48/0.88  fof(f2227,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_9 | spl8_16 | ~spl8_17 | ~spl8_18 | ~spl8_39 | ~spl8_45)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2226,f149])).
% 3.48/0.88  fof(f149,plain,(
% 3.48/0.88    l1_pre_topc(sK0) | ~spl8_9),
% 3.48/0.88    inference(avatar_component_clause,[],[f147])).
% 3.48/0.88  fof(f2226,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_16 | ~spl8_17 | ~spl8_18 | ~spl8_39 | ~spl8_45)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2225,f217])).
% 3.48/0.88  fof(f217,plain,(
% 3.48/0.88    ~v2_struct_0(sK2(sK5(sK0))) | spl8_16),
% 3.48/0.88    inference(avatar_component_clause,[],[f215])).
% 3.48/0.88  fof(f2225,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | v2_struct_0(sK2(sK5(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_17 | ~spl8_18 | ~spl8_39 | ~spl8_45)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2224,f261])).
% 3.48/0.88  fof(f261,plain,(
% 3.48/0.88    v4_orders_2(sK2(sK5(sK0))) | ~spl8_17),
% 3.48/0.88    inference(avatar_component_clause,[],[f259])).
% 3.48/0.88  fof(f2224,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | ~v4_orders_2(sK2(sK5(sK0))) | v2_struct_0(sK2(sK5(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_18 | ~spl8_39 | ~spl8_45)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2223,f288])).
% 3.48/0.88  fof(f288,plain,(
% 3.48/0.88    v7_waybel_0(sK2(sK5(sK0))) | ~spl8_18),
% 3.48/0.88    inference(avatar_component_clause,[],[f286])).
% 3.48/0.88  fof(f2223,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | ~v4_orders_2(sK2(sK5(sK0))) | v2_struct_0(sK2(sK5(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_39 | ~spl8_45)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2222,f2021])).
% 3.48/0.88  fof(f2021,plain,(
% 3.48/0.88    l1_waybel_0(sK2(sK5(sK0)),sK0) | ~spl8_39),
% 3.48/0.88    inference(avatar_component_clause,[],[f2020])).
% 3.48/0.88  fof(f2222,plain,(
% 3.48/0.88    ~v3_yellow_6(sK2(sK5(sK0)),sK0) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | ~v4_orders_2(sK2(sK5(sK0))) | v2_struct_0(sK2(sK5(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_45),
% 3.48/0.88    inference(trivial_inequality_removal,[],[f2209])).
% 3.48/0.88  fof(f2209,plain,(
% 3.48/0.88    k1_xboole_0 != k1_xboole_0 | ~v3_yellow_6(sK2(sK5(sK0)),sK0) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | ~v4_orders_2(sK2(sK5(sK0))) | v2_struct_0(sK2(sK5(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_45),
% 3.48/0.88    inference(superposition,[],[f75,f2181])).
% 3.48/0.88  fof(f2181,plain,(
% 3.48/0.88    k1_xboole_0 = k10_yellow_6(sK0,sK2(sK5(sK0))) | ~spl8_45),
% 3.48/0.88    inference(avatar_component_clause,[],[f2179])).
% 3.48/0.88  fof(f75,plain,(
% 3.48/0.88    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f48])).
% 3.48/0.88  fof(f48,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(nnf_transformation,[],[f21])).
% 3.48/0.88  fof(f21,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(flattening,[],[f20])).
% 3.48/0.88  fof(f20,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f10])).
% 3.48/0.88  fof(f10,axiom,(
% 3.48/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).
% 3.48/0.88  fof(f2182,plain,(
% 3.48/0.88    spl8_45 | ~spl8_40),
% 3.48/0.88    inference(avatar_split_clause,[],[f2143,f2024,f2179])).
% 3.48/0.88  fof(f2024,plain,(
% 3.48/0.88    spl8_40 <=> ! [X1,X0] : (~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 3.48/0.88  fof(f2143,plain,(
% 3.48/0.88    k1_xboole_0 = k10_yellow_6(sK0,sK2(sK5(sK0))) | ~spl8_40),
% 3.48/0.88    inference(resolution,[],[f2111,f173])).
% 3.48/0.88  fof(f173,plain,(
% 3.48/0.88    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 3.48/0.88    inference(resolution,[],[f99,f167])).
% 3.48/0.88  fof(f167,plain,(
% 3.48/0.88    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.48/0.88    inference(resolution,[],[f102,f100])).
% 3.48/0.88  fof(f100,plain,(
% 3.48/0.88    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.48/0.88    inference(cnf_transformation,[],[f3])).
% 3.48/0.88  fof(f3,axiom,(
% 3.48/0.88    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 3.48/0.88  fof(f102,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f60])).
% 3.48/0.88  fof(f60,plain,(
% 3.48/0.88    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.48/0.88    inference(nnf_transformation,[],[f4])).
% 3.48/0.88  fof(f4,axiom,(
% 3.48/0.88    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.48/0.88  fof(f99,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f59])).
% 3.48/0.88  fof(f59,plain,(
% 3.48/0.88    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.48/0.88    inference(flattening,[],[f58])).
% 3.48/0.88  fof(f58,plain,(
% 3.48/0.88    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.48/0.88    inference(nnf_transformation,[],[f2])).
% 3.48/0.88  fof(f2,axiom,(
% 3.48/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.48/0.88  fof(f2111,plain,(
% 3.48/0.88    ( ! [X0] : (r1_tarski(k10_yellow_6(sK0,sK2(sK5(sK0))),X0)) ) | ~spl8_40),
% 3.48/0.88    inference(resolution,[],[f2025,f108])).
% 3.48/0.88  fof(f108,plain,(
% 3.48/0.88    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.48/0.88    inference(equality_resolution,[],[f98])).
% 3.48/0.88  fof(f98,plain,(
% 3.48/0.88    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.48/0.88    inference(cnf_transformation,[],[f59])).
% 3.48/0.88  fof(f2025,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1)) ) | ~spl8_40),
% 3.48/0.88    inference(avatar_component_clause,[],[f2024])).
% 3.48/0.88  fof(f2055,plain,(
% 3.48/0.88    ~spl8_8 | spl8_11 | ~spl8_12 | spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_38 | spl8_39),
% 3.48/0.88    inference(avatar_contradiction_clause,[],[f2054])).
% 3.48/0.88  fof(f2054,plain,(
% 3.48/0.88    $false | (~spl8_8 | spl8_11 | ~spl8_12 | spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_38 | spl8_39)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2053,f204])).
% 3.48/0.88  fof(f2053,plain,(
% 3.48/0.88    v2_struct_0(sK5(sK0)) | (~spl8_8 | spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15 | ~spl8_38 | spl8_39)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2052,f208])).
% 3.48/0.88  fof(f2052,plain,(
% 3.48/0.88    ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | (~spl8_8 | spl8_11 | ~spl8_12 | ~spl8_15 | ~spl8_38 | spl8_39)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2051,f212])).
% 3.48/0.88  fof(f2051,plain,(
% 3.48/0.88    ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | (~spl8_8 | spl8_11 | ~spl8_12 | ~spl8_38 | spl8_39)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2049,f2017])).
% 3.48/0.88  fof(f2049,plain,(
% 3.48/0.88    ~l1_waybel_0(sK5(sK0),sK0) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | (~spl8_8 | spl8_11 | ~spl8_12 | spl8_39)),
% 3.48/0.88    inference(resolution,[],[f2022,f238])).
% 3.48/0.88  fof(f238,plain,(
% 3.48/0.88    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) ) | (~spl8_8 | spl8_11 | ~spl8_12)),
% 3.48/0.88    inference(subsumption_resolution,[],[f237,f159])).
% 3.48/0.88  fof(f237,plain,(
% 3.48/0.88    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl8_8 | ~spl8_12)),
% 3.48/0.88    inference(subsumption_resolution,[],[f236,f165])).
% 3.48/0.88  fof(f165,plain,(
% 3.48/0.88    l1_struct_0(sK0) | ~spl8_12),
% 3.48/0.88    inference(avatar_component_clause,[],[f163])).
% 3.48/0.88  fof(f163,plain,(
% 3.48/0.88    spl8_12 <=> l1_struct_0(sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 3.48/0.88  fof(f236,plain,(
% 3.48/0.88    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl8_8),
% 3.48/0.88    inference(duplicate_literal_removal,[],[f235])).
% 3.48/0.88  fof(f235,plain,(
% 3.48/0.88    ( ! [X0] : (l1_waybel_0(sK2(X0),sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0)) ) | ~spl8_8),
% 3.48/0.88    inference(resolution,[],[f80,f144])).
% 3.48/0.88  fof(f144,plain,(
% 3.48/0.88    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl8_8),
% 3.48/0.88    inference(avatar_component_clause,[],[f143])).
% 3.48/0.88  fof(f143,plain,(
% 3.48/0.88    spl8_8 <=> ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 3.48/0.88  fof(f80,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f23])).
% 3.48/0.88  fof(f23,plain,(
% 3.48/0.88    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(flattening,[],[f22])).
% 3.48/0.88  fof(f22,plain,(
% 3.48/0.88    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f9])).
% 3.48/0.88  fof(f9,axiom,(
% 3.48/0.88    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 3.48/0.88  fof(f2022,plain,(
% 3.48/0.88    ~l1_waybel_0(sK2(sK5(sK0)),sK0) | spl8_39),
% 3.48/0.88    inference(avatar_component_clause,[],[f2020])).
% 3.48/0.88  fof(f2034,plain,(
% 3.48/0.88    spl8_1 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_38),
% 3.48/0.88    inference(avatar_contradiction_clause,[],[f2033])).
% 3.48/0.88  fof(f2033,plain,(
% 3.48/0.88    $false | (spl8_1 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_38)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2032,f159])).
% 3.48/0.88  fof(f2032,plain,(
% 3.48/0.88    v2_struct_0(sK0) | (spl8_1 | ~spl8_9 | ~spl8_10 | spl8_38)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2031,f154])).
% 3.48/0.88  fof(f2031,plain,(
% 3.48/0.88    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_9 | spl8_38)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2030,f149])).
% 3.48/0.88  fof(f2030,plain,(
% 3.48/0.88    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_38)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2028,f113])).
% 3.48/0.88  fof(f113,plain,(
% 3.48/0.88    ~v1_compts_1(sK0) | spl8_1),
% 3.48/0.88    inference(avatar_component_clause,[],[f111])).
% 3.48/0.88  fof(f111,plain,(
% 3.48/0.88    spl8_1 <=> v1_compts_1(sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.48/0.88  fof(f2028,plain,(
% 3.48/0.88    v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_38),
% 3.48/0.88    inference(resolution,[],[f2018,f93])).
% 3.48/0.88  fof(f93,plain,(
% 3.48/0.88    ( ! [X0] : (l1_waybel_0(sK5(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f57])).
% 3.48/0.88  fof(f57,plain,(
% 3.48/0.88    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK5(X0),k6_yellow_6(X0)) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f54,f56,f55])).
% 3.48/0.88  fof(f55,plain,(
% 3.48/0.88    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK5(X0),k6_yellow_6(X0)) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0))))),
% 3.48/0.88    introduced(choice_axiom,[])).
% 3.48/0.88  fof(f56,plain,(
% 3.48/0.88    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))))),
% 3.48/0.88    introduced(choice_axiom,[])).
% 3.48/0.88  fof(f54,plain,(
% 3.48/0.88    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(rectify,[],[f53])).
% 3.48/0.88  fof(f53,plain,(
% 3.48/0.88    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(nnf_transformation,[],[f35])).
% 3.48/0.88  fof(f35,plain,(
% 3.48/0.88    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(flattening,[],[f34])).
% 3.48/0.88  fof(f34,plain,(
% 3.48/0.88    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f15])).
% 3.48/0.88  fof(f15,axiom,(
% 3.48/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).
% 3.48/0.88  fof(f2018,plain,(
% 3.48/0.88    ~l1_waybel_0(sK5(sK0),sK0) | spl8_38),
% 3.48/0.88    inference(avatar_component_clause,[],[f2016])).
% 3.48/0.88  fof(f2026,plain,(
% 3.48/0.88    ~spl8_38 | ~spl8_39 | spl8_40 | spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_13 | ~spl8_14 | ~spl8_15 | spl8_16 | ~spl8_17 | ~spl8_18),
% 3.48/0.88    inference(avatar_split_clause,[],[f2014,f286,f259,f215,f211,f207,f203,f157,f152,f147,f143,f111,f2024,f2020,f2016])).
% 3.48/0.88  fof(f2014,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_13 | ~spl8_14 | ~spl8_15 | spl8_16 | ~spl8_17 | ~spl8_18)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2013,f212])).
% 3.48/0.88  fof(f2013,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_13 | ~spl8_14 | spl8_16 | ~spl8_17 | ~spl8_18)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2012,f208])).
% 3.48/0.88  fof(f2012,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_13 | spl8_16 | ~spl8_17 | ~spl8_18)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2011,f204])).
% 3.48/0.88  fof(f2011,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_16 | ~spl8_17 | ~spl8_18)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2010,f113])).
% 3.48/0.88  fof(f2010,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | v1_compts_1(sK0) | v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_16 | ~spl8_17 | ~spl8_18)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2009,f288])).
% 3.48/0.88  fof(f2009,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | v1_compts_1(sK0) | v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_16 | ~spl8_17)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2008,f159])).
% 3.48/0.88  fof(f2008,plain,(
% 3.48/0.88    ( ! [X0,X1] : (v2_struct_0(sK0) | ~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | v1_compts_1(sK0) | v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_16 | ~spl8_17)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2007,f154])).
% 3.48/0.88  fof(f2007,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | v1_compts_1(sK0) | v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (~spl8_8 | ~spl8_9 | spl8_16 | ~spl8_17)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2006,f149])).
% 3.48/0.88  fof(f2006,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | v1_compts_1(sK0) | v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (~spl8_8 | spl8_16 | ~spl8_17)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2005,f217])).
% 3.48/0.88  fof(f2005,plain,(
% 3.48/0.88    ( ! [X0,X1] : (v2_struct_0(sK2(sK5(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | v1_compts_1(sK0) | v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | (~spl8_8 | ~spl8_17)),
% 3.48/0.88    inference(subsumption_resolution,[],[f2002,f261])).
% 3.48/0.88  fof(f2002,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~v4_orders_2(sK2(sK5(sK0))) | v2_struct_0(sK2(sK5(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X0,k10_yellow_6(sK0,sK2(sK5(sK0)))) | r1_tarski(X0,X1) | ~l1_waybel_0(sK2(sK5(sK0)),sK0) | ~v7_waybel_0(sK2(sK5(sK0))) | v1_compts_1(sK0) | v2_struct_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | ~v7_waybel_0(sK5(sK0)) | ~l1_waybel_0(sK5(sK0),sK0)) ) | ~spl8_8),
% 3.48/0.88    inference(resolution,[],[f1004,f144])).
% 3.48/0.88  fof(f1004,plain,(
% 3.48/0.88    ( ! [X2,X0,X3,X1] : (~m2_yellow_6(X0,X1,sK5(X1)) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | r1_tarski(X2,X3) | ~l1_waybel_0(X0,X1) | ~v7_waybel_0(X0) | v1_compts_1(X1)) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f1003,f391])).
% 3.48/0.88  fof(f391,plain,(
% 3.48/0.88    ( ! [X6,X4,X5,X3] : (m1_subset_1(sK7(X5,X6),u1_struct_0(X4)) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,X4) | ~r1_tarski(X5,k10_yellow_6(X4,X3)) | r1_tarski(X5,X6)) )),
% 3.48/0.88    inference(resolution,[],[f247,f176])).
% 3.48/0.88  fof(f176,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 3.48/0.88    inference(resolution,[],[f105,f106])).
% 3.48/0.88  fof(f106,plain,(
% 3.48/0.88    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f64])).
% 3.48/0.88  fof(f64,plain,(
% 3.48/0.88    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.48/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).
% 3.48/0.88  fof(f63,plain,(
% 3.48/0.88    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 3.48/0.88    introduced(choice_axiom,[])).
% 3.48/0.88  fof(f62,plain,(
% 3.48/0.88    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.48/0.88    inference(rectify,[],[f61])).
% 3.48/0.88  fof(f61,plain,(
% 3.48/0.88    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.48/0.88    inference(nnf_transformation,[],[f40])).
% 3.48/0.88  fof(f40,plain,(
% 3.48/0.88    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f1])).
% 3.48/0.88  fof(f1,axiom,(
% 3.48/0.88    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.48/0.88  fof(f105,plain,(
% 3.48/0.88    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f64])).
% 3.48/0.88  fof(f247,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X1,X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X0,X1)) )),
% 3.48/0.88    inference(resolution,[],[f84,f101])).
% 3.48/0.88  fof(f101,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f38])).
% 3.48/0.88  fof(f38,plain,(
% 3.48/0.88    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.48/0.88    inference(flattening,[],[f37])).
% 3.48/0.88  fof(f37,plain,(
% 3.48/0.88    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.48/0.88    inference(ennf_transformation,[],[f5])).
% 3.48/0.88  fof(f5,axiom,(
% 3.48/0.88    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 3.48/0.88  fof(f84,plain,(
% 3.48/0.88    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f29])).
% 3.48/0.88  fof(f29,plain,(
% 3.48/0.88    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(flattening,[],[f28])).
% 3.48/0.88  fof(f28,plain,(
% 3.48/0.88    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f8])).
% 3.48/0.88  fof(f8,axiom,(
% 3.48/0.88    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 3.48/0.88  fof(f1003,plain,(
% 3.48/0.88    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | r1_tarski(X2,X3) | ~l1_waybel_0(X0,X1) | ~m2_yellow_6(X0,X1,sK5(X1)) | v1_compts_1(X1) | ~m1_subset_1(sK7(X2,X3),u1_struct_0(X1))) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f1002,f90])).
% 3.48/0.88  fof(f90,plain,(
% 3.48/0.88    ( ! [X0] : (~v2_struct_0(sK5(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f57])).
% 3.48/0.88  fof(f1002,plain,(
% 3.48/0.88    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | r1_tarski(X2,X3) | ~l1_waybel_0(X0,X1) | ~m2_yellow_6(X0,X1,sK5(X1)) | v2_struct_0(sK5(X1)) | v1_compts_1(X1) | ~m1_subset_1(sK7(X2,X3),u1_struct_0(X1))) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f1001,f91])).
% 3.48/0.88  fof(f91,plain,(
% 3.48/0.88    ( ! [X0] : (v4_orders_2(sK5(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f57])).
% 3.48/0.88  fof(f1001,plain,(
% 3.48/0.88    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | r1_tarski(X2,X3) | ~l1_waybel_0(X0,X1) | ~m2_yellow_6(X0,X1,sK5(X1)) | ~v4_orders_2(sK5(X1)) | v2_struct_0(sK5(X1)) | v1_compts_1(X1) | ~m1_subset_1(sK7(X2,X3),u1_struct_0(X1))) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f1000,f92])).
% 3.48/0.88  fof(f92,plain,(
% 3.48/0.88    ( ! [X0] : (v7_waybel_0(sK5(X0)) | v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f57])).
% 3.48/0.88  fof(f1000,plain,(
% 3.48/0.88    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | r1_tarski(X2,X3) | ~l1_waybel_0(X0,X1) | ~m2_yellow_6(X0,X1,sK5(X1)) | ~v7_waybel_0(sK5(X1)) | ~v4_orders_2(sK5(X1)) | v2_struct_0(sK5(X1)) | v1_compts_1(X1) | ~m1_subset_1(sK7(X2,X3),u1_struct_0(X1))) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f999,f93])).
% 3.48/0.88  fof(f999,plain,(
% 3.48/0.88    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | r1_tarski(X2,X3) | ~l1_waybel_0(X0,X1) | ~m2_yellow_6(X0,X1,sK5(X1)) | ~l1_waybel_0(sK5(X1),X1) | ~v7_waybel_0(sK5(X1)) | ~v4_orders_2(sK5(X1)) | v2_struct_0(sK5(X1)) | v1_compts_1(X1) | ~m1_subset_1(sK7(X2,X3),u1_struct_0(X1))) )),
% 3.48/0.88    inference(duplicate_literal_removal,[],[f992])).
% 3.48/0.88  fof(f992,plain,(
% 3.48/0.88    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | r1_tarski(X2,X3) | ~l1_waybel_0(X0,X1) | ~m2_yellow_6(X0,X1,sK5(X1)) | ~l1_waybel_0(sK5(X1),X1) | ~v7_waybel_0(sK5(X1)) | ~v4_orders_2(sK5(X1)) | v2_struct_0(sK5(X1)) | v1_compts_1(X1) | ~m1_subset_1(sK7(X2,X3),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.48/0.88    inference(resolution,[],[f772,f95])).
% 3.48/0.88  fof(f95,plain,(
% 3.48/0.88    ( ! [X2,X0] : (~r3_waybel_9(X0,sK5(X0),X2) | v1_compts_1(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f57])).
% 3.48/0.88  fof(f772,plain,(
% 3.48/0.88    ( ! [X10,X8,X7,X11,X9] : (r3_waybel_9(X8,X11,sK7(X9,X10)) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~r1_tarski(X9,k10_yellow_6(X8,X7)) | r1_tarski(X9,X10) | ~l1_waybel_0(X7,X8) | ~m2_yellow_6(X7,X8,X11) | ~l1_waybel_0(X11,X8) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11)) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f764,f391])).
% 3.48/0.88  fof(f764,plain,(
% 3.48/0.88    ( ! [X10,X8,X7,X11,X9] : (~l1_waybel_0(X7,X8) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~r1_tarski(X9,k10_yellow_6(X8,X7)) | r1_tarski(X9,X10) | r3_waybel_9(X8,X11,sK7(X9,X10)) | ~m1_subset_1(sK7(X9,X10),u1_struct_0(X8)) | ~m2_yellow_6(X7,X8,X11) | ~l1_waybel_0(X11,X8) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11)) )),
% 3.48/0.88    inference(duplicate_literal_removal,[],[f761])).
% 3.48/0.88  fof(f761,plain,(
% 3.48/0.88    ( ! [X10,X8,X7,X11,X9] : (~l1_waybel_0(X7,X8) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~r1_tarski(X9,k10_yellow_6(X8,X7)) | r1_tarski(X9,X10) | r3_waybel_9(X8,X11,sK7(X9,X10)) | ~m1_subset_1(sK7(X9,X10),u1_struct_0(X8)) | ~m2_yellow_6(X7,X8,X11) | ~l1_waybel_0(X11,X8) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 3.48/0.88    inference(resolution,[],[f758,f81])).
% 3.48/0.88  fof(f81,plain,(
% 3.48/0.88    ( ! [X2,X0,X3,X1] : (~r3_waybel_9(X0,X2,X3) | r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f25])).
% 3.48/0.88  fof(f25,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(flattening,[],[f24])).
% 3.48/0.88  fof(f24,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f12])).
% 3.48/0.88  fof(f12,axiom,(
% 3.48/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).
% 3.48/0.88  fof(f758,plain,(
% 3.48/0.88    ( ! [X6,X4,X5,X3] : (r3_waybel_9(X3,X4,sK7(X5,X6)) | ~l1_waybel_0(X4,X3) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r1_tarski(X5,k10_yellow_6(X3,X4)) | r1_tarski(X5,X6)) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f276,f391])).
% 3.48/0.88  fof(f276,plain,(
% 3.48/0.88    ( ! [X6,X4,X5,X3] : (r3_waybel_9(X3,X4,sK7(X5,X6)) | ~m1_subset_1(sK7(X5,X6),u1_struct_0(X3)) | ~l1_waybel_0(X4,X3) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r1_tarski(X5,k10_yellow_6(X3,X4)) | r1_tarski(X5,X6)) )),
% 3.48/0.88    inference(resolution,[],[f85,f176])).
% 3.48/0.88  fof(f85,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f31])).
% 3.48/0.88  fof(f31,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(flattening,[],[f30])).
% 3.48/0.88  fof(f30,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f11])).
% 3.48/0.88  fof(f11,axiom,(
% 3.48/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).
% 3.48/0.88  fof(f656,plain,(
% 3.48/0.88    ~spl8_28),
% 3.48/0.88    inference(avatar_contradiction_clause,[],[f655])).
% 3.48/0.88  fof(f655,plain,(
% 3.48/0.88    $false | ~spl8_28),
% 3.48/0.88    inference(subsumption_resolution,[],[f651,f167])).
% 3.48/0.88  fof(f651,plain,(
% 3.48/0.88    ~r1_tarski(k1_xboole_0,sK4(sK0,sK1)) | ~spl8_28),
% 3.48/0.88    inference(resolution,[],[f628,f104])).
% 3.48/0.88  fof(f104,plain,(
% 3.48/0.88    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f39])).
% 3.48/0.88  fof(f39,plain,(
% 3.48/0.88    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.48/0.88    inference(ennf_transformation,[],[f6])).
% 3.48/0.88  fof(f6,axiom,(
% 3.48/0.88    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.48/0.88  fof(f628,plain,(
% 3.48/0.88    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~spl8_28),
% 3.48/0.88    inference(avatar_component_clause,[],[f626])).
% 3.48/0.88  fof(f626,plain,(
% 3.48/0.88    spl8_28 <=> r2_hidden(sK4(sK0,sK1),k1_xboole_0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 3.48/0.88  fof(f629,plain,(
% 3.48/0.88    spl8_28 | ~spl8_25 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11),
% 3.48/0.88    inference(avatar_split_clause,[],[f624,f157,f152,f147,f134,f129,f124,f119,f115,f111,f514,f626])).
% 3.48/0.88  fof(f514,plain,(
% 3.48/0.88    spl8_25 <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 3.48/0.88  fof(f115,plain,(
% 3.48/0.88    spl8_2 <=> ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1))),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.48/0.88  fof(f119,plain,(
% 3.48/0.88    spl8_3 <=> l1_waybel_0(sK1,sK0)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.48/0.88  fof(f124,plain,(
% 3.48/0.88    spl8_4 <=> v7_waybel_0(sK1)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.48/0.88  fof(f129,plain,(
% 3.48/0.88    spl8_5 <=> v4_orders_2(sK1)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.48/0.88  fof(f134,plain,(
% 3.48/0.88    spl8_6 <=> v2_struct_0(sK1)),
% 3.48/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.48/0.88  fof(f624,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f623,f159])).
% 3.48/0.88  fof(f623,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f622,f154])).
% 3.48/0.88  fof(f622,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f621,f149])).
% 3.48/0.88  fof(f621,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f620,f112])).
% 3.48/0.88  fof(f112,plain,(
% 3.48/0.88    v1_compts_1(sK0) | ~spl8_1),
% 3.48/0.88    inference(avatar_component_clause,[],[f111])).
% 3.48/0.88  fof(f620,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f619,f136])).
% 3.48/0.88  fof(f136,plain,(
% 3.48/0.88    ~v2_struct_0(sK1) | spl8_6),
% 3.48/0.88    inference(avatar_component_clause,[],[f134])).
% 3.48/0.88  fof(f619,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f618,f131])).
% 3.48/0.88  fof(f131,plain,(
% 3.48/0.88    v4_orders_2(sK1) | ~spl8_5),
% 3.48/0.88    inference(avatar_component_clause,[],[f129])).
% 3.48/0.88  fof(f618,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f617,f126])).
% 3.48/0.88  fof(f126,plain,(
% 3.48/0.88    v7_waybel_0(sK1) | ~spl8_4),
% 3.48/0.88    inference(avatar_component_clause,[],[f124])).
% 3.48/0.88  fof(f617,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f612,f121])).
% 3.48/0.88  fof(f121,plain,(
% 3.48/0.88    l1_waybel_0(sK1,sK0) | ~spl8_3),
% 3.48/0.88    inference(avatar_component_clause,[],[f119])).
% 3.48/0.88  fof(f612,plain,(
% 3.48/0.88    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(resolution,[],[f611,f87])).
% 3.48/0.88  fof(f87,plain,(
% 3.48/0.88    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f52])).
% 3.48/0.88  fof(f52,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f51])).
% 3.48/0.88  fof(f51,plain,(
% 3.48/0.88    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.48/0.88    introduced(choice_axiom,[])).
% 3.48/0.88  fof(f33,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(flattening,[],[f32])).
% 3.48/0.88  fof(f32,plain,(
% 3.48/0.88    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f14])).
% 3.48/0.88  fof(f14,axiom,(
% 3.48/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).
% 3.48/0.88  fof(f611,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f610,f159])).
% 3.48/0.88  fof(f610,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f609,f154])).
% 3.48/0.88  fof(f609,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f608,f149])).
% 3.48/0.88  fof(f608,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f607,f136])).
% 3.48/0.88  fof(f607,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f606,f131])).
% 3.48/0.88  fof(f606,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f605,f126])).
% 3.48/0.88  fof(f605,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f604,f121])).
% 3.48/0.88  fof(f604,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(duplicate_literal_removal,[],[f603])).
% 3.48/0.88  fof(f603,plain,(
% 3.48/0.88    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(resolution,[],[f578,f350])).
% 3.48/0.88  fof(f350,plain,(
% 3.48/0.88    ( ! [X12] : (~v3_yellow_6(sK3(sK0,sK1,X12),sK0) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X12)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11)),
% 3.48/0.88    inference(subsumption_resolution,[],[f349,f159])).
% 3.48/0.88  fof(f349,plain,(
% 3.48/0.88    ( ! [X12] : (~r3_waybel_9(sK0,sK1,X12) | ~m1_subset_1(X12,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v3_yellow_6(sK3(sK0,sK1,X12),sK0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10)),
% 3.48/0.88    inference(subsumption_resolution,[],[f348,f154])).
% 3.48/0.88  fof(f348,plain,(
% 3.48/0.88    ( ! [X12] : (~r3_waybel_9(sK0,sK1,X12) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK3(sK0,sK1,X12),sK0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9)),
% 3.48/0.88    inference(subsumption_resolution,[],[f347,f149])).
% 3.48/0.88  fof(f347,plain,(
% 3.48/0.88    ( ! [X12] : (~r3_waybel_9(sK0,sK1,X12) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK3(sK0,sK1,X12),sK0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6)),
% 3.48/0.88    inference(subsumption_resolution,[],[f346,f136])).
% 3.48/0.88  fof(f346,plain,(
% 3.48/0.88    ( ! [X12] : (~r3_waybel_9(sK0,sK1,X12) | ~m1_subset_1(X12,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK3(sK0,sK1,X12),sK0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5)),
% 3.48/0.88    inference(subsumption_resolution,[],[f345,f131])).
% 3.48/0.88  fof(f345,plain,(
% 3.48/0.88    ( ! [X12] : (~r3_waybel_9(sK0,sK1,X12) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK3(sK0,sK1,X12),sK0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.48/0.88    inference(subsumption_resolution,[],[f344,f126])).
% 3.48/0.88  fof(f344,plain,(
% 3.48/0.88    ( ! [X12] : (~r3_waybel_9(sK0,sK1,X12) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK3(sK0,sK1,X12),sK0)) ) | (~spl8_2 | ~spl8_3)),
% 3.48/0.88    inference(subsumption_resolution,[],[f335,f121])).
% 3.48/0.88  fof(f335,plain,(
% 3.48/0.88    ( ! [X12] : (~r3_waybel_9(sK0,sK1,X12) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_yellow_6(sK3(sK0,sK1,X12),sK0)) ) | ~spl8_2),
% 3.48/0.88    inference(resolution,[],[f82,f116])).
% 3.48/0.88  fof(f116,plain,(
% 3.48/0.88    ( ! [X2] : (~m2_yellow_6(X2,sK0,sK1) | ~v3_yellow_6(X2,sK0)) ) | ~spl8_2),
% 3.48/0.88    inference(avatar_component_clause,[],[f115])).
% 3.48/0.88  fof(f82,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (m2_yellow_6(sK3(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f50])).
% 3.48/0.88  fof(f50,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f49])).
% 3.48/0.88  fof(f49,plain,(
% 3.48/0.88    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)))),
% 3.48/0.88    introduced(choice_axiom,[])).
% 3.48/0.88  fof(f27,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.88    inference(flattening,[],[f26])).
% 3.48/0.88  fof(f26,plain,(
% 3.48/0.88    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.48/0.88    inference(ennf_transformation,[],[f13])).
% 3.48/0.88  fof(f13,axiom,(
% 3.48/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).
% 3.48/0.88  fof(f578,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (v3_yellow_6(sK3(X0,X1,X2),X0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(X2,k1_xboole_0)) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f577,f343])).
% 3.48/0.88  fof(f343,plain,(
% 3.48/0.88    ( ! [X10,X11,X9] : (~v2_struct_0(sK3(X9,X10,X11)) | ~m1_subset_1(X11,u1_struct_0(X9)) | ~l1_waybel_0(X10,X9) | ~v7_waybel_0(X10) | ~v4_orders_2(X10) | v2_struct_0(X10) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9) | ~r3_waybel_9(X9,X10,X11)) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f336,f96])).
% 3.48/0.88  fof(f96,plain,(
% 3.48/0.88    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f36])).
% 3.48/0.88  fof(f36,plain,(
% 3.48/0.88    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.48/0.88    inference(ennf_transformation,[],[f7])).
% 3.48/0.88  fof(f7,axiom,(
% 3.48/0.88    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.48/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.48/0.88  fof(f336,plain,(
% 3.48/0.88    ( ! [X10,X11,X9] : (~r3_waybel_9(X9,X10,X11) | ~m1_subset_1(X11,u1_struct_0(X9)) | ~l1_waybel_0(X10,X9) | ~v7_waybel_0(X10) | ~v4_orders_2(X10) | v2_struct_0(X10) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9) | ~v2_struct_0(sK3(X9,X10,X11)) | ~l1_struct_0(X9)) )),
% 3.48/0.88    inference(duplicate_literal_removal,[],[f334])).
% 3.48/0.88  fof(f334,plain,(
% 3.48/0.88    ( ! [X10,X11,X9] : (~r3_waybel_9(X9,X10,X11) | ~m1_subset_1(X11,u1_struct_0(X9)) | ~l1_waybel_0(X10,X9) | ~v7_waybel_0(X10) | ~v4_orders_2(X10) | v2_struct_0(X10) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9) | ~v2_struct_0(sK3(X9,X10,X11)) | ~l1_waybel_0(X10,X9) | ~v7_waybel_0(X10) | ~v4_orders_2(X10) | v2_struct_0(X10) | ~l1_struct_0(X9) | v2_struct_0(X9)) )),
% 3.48/0.88    inference(resolution,[],[f82,f77])).
% 3.48/0.88  fof(f77,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | ~v2_struct_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f23])).
% 3.48/0.88  fof(f577,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_xboole_0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v3_yellow_6(sK3(X0,X1,X2),X0) | v2_struct_0(sK3(X0,X1,X2))) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f576,f342])).
% 3.48/0.88  fof(f342,plain,(
% 3.48/0.88    ( ! [X6,X8,X7] : (v4_orders_2(sK3(X6,X7,X8)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_waybel_0(X7,X6) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~r3_waybel_9(X6,X7,X8)) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f337,f96])).
% 3.48/0.88  fof(f337,plain,(
% 3.48/0.88    ( ! [X6,X8,X7] : (~r3_waybel_9(X6,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_waybel_0(X7,X6) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | v4_orders_2(sK3(X6,X7,X8)) | ~l1_struct_0(X6)) )),
% 3.48/0.88    inference(duplicate_literal_removal,[],[f333])).
% 3.48/0.88  fof(f333,plain,(
% 3.48/0.88    ( ! [X6,X8,X7] : (~r3_waybel_9(X6,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_waybel_0(X7,X6) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | v4_orders_2(sK3(X6,X7,X8)) | ~l1_waybel_0(X7,X6) | ~v7_waybel_0(X7) | ~v4_orders_2(X7) | v2_struct_0(X7) | ~l1_struct_0(X6) | v2_struct_0(X6)) )),
% 3.48/0.88    inference(resolution,[],[f82,f78])).
% 3.48/0.88  fof(f78,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v4_orders_2(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f23])).
% 3.48/0.88  fof(f576,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_xboole_0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v3_yellow_6(sK3(X0,X1,X2),X0) | ~v4_orders_2(sK3(X0,X1,X2)) | v2_struct_0(sK3(X0,X1,X2))) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f575,f341])).
% 3.48/0.88  fof(f341,plain,(
% 3.48/0.88    ( ! [X4,X5,X3] : (v7_waybel_0(sK3(X3,X4,X5)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(X4,X3) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r3_waybel_9(X3,X4,X5)) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f338,f96])).
% 3.48/0.88  fof(f338,plain,(
% 3.48/0.88    ( ! [X4,X5,X3] : (~r3_waybel_9(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(X4,X3) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | v7_waybel_0(sK3(X3,X4,X5)) | ~l1_struct_0(X3)) )),
% 3.48/0.88    inference(duplicate_literal_removal,[],[f332])).
% 3.48/0.88  fof(f332,plain,(
% 3.48/0.88    ( ! [X4,X5,X3] : (~r3_waybel_9(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(X4,X3) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | v7_waybel_0(sK3(X3,X4,X5)) | ~l1_waybel_0(X4,X3) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 3.48/0.88    inference(resolution,[],[f82,f79])).
% 3.48/0.88  fof(f79,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (~m2_yellow_6(X2,X0,X1) | v7_waybel_0(X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.48/0.88    inference(cnf_transformation,[],[f23])).
% 3.48/0.88  fof(f575,plain,(
% 3.48/0.88    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_xboole_0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v3_yellow_6(sK3(X0,X1,X2),X0) | ~v7_waybel_0(sK3(X0,X1,X2)) | ~v4_orders_2(sK3(X0,X1,X2)) | v2_struct_0(sK3(X0,X1,X2))) )),
% 3.48/0.88    inference(subsumption_resolution,[],[f362,f340])).
% 3.48/0.89  fof(f340,plain,(
% 3.48/0.89    ( ! [X2,X0,X1] : (l1_waybel_0(sK3(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r3_waybel_9(X0,X1,X2)) )),
% 3.48/0.89    inference(subsumption_resolution,[],[f339,f96])).
% 3.68/0.89  fof(f339,plain,(
% 3.68/0.89    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | l1_waybel_0(sK3(X0,X1,X2),X0) | ~l1_struct_0(X0)) )),
% 3.68/0.89    inference(duplicate_literal_removal,[],[f331])).
% 3.68/0.89  fof(f331,plain,(
% 3.68/0.89    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | l1_waybel_0(sK3(X0,X1,X2),X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.68/0.89    inference(resolution,[],[f82,f80])).
% 3.68/0.89  fof(f362,plain,(
% 3.68/0.89    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_xboole_0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v3_yellow_6(sK3(X0,X1,X2),X0) | ~l1_waybel_0(sK3(X0,X1,X2),X0) | ~v7_waybel_0(sK3(X0,X1,X2)) | ~v4_orders_2(sK3(X0,X1,X2)) | v2_struct_0(sK3(X0,X1,X2))) )),
% 3.68/0.89    inference(duplicate_literal_removal,[],[f361])).
% 3.68/0.89  fof(f361,plain,(
% 3.68/0.89    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_xboole_0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v3_yellow_6(sK3(X0,X1,X2),X0) | ~l1_waybel_0(sK3(X0,X1,X2),X0) | ~v7_waybel_0(sK3(X0,X1,X2)) | ~v4_orders_2(sK3(X0,X1,X2)) | v2_struct_0(sK3(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.68/0.89    inference(superposition,[],[f83,f76])).
% 3.68/0.89  fof(f76,plain,(
% 3.68/0.89    ( ! [X0,X1] : (k1_xboole_0 = k10_yellow_6(X0,X1) | v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.68/0.89    inference(cnf_transformation,[],[f48])).
% 3.68/0.89  fof(f83,plain,(
% 3.68/0.89    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.68/0.89    inference(cnf_transformation,[],[f50])).
% 3.68/0.89  fof(f574,plain,(
% 3.68/0.89    ~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_25),
% 3.68/0.89    inference(avatar_contradiction_clause,[],[f573])).
% 3.68/0.89  fof(f573,plain,(
% 3.68/0.89    $false | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_25)),
% 3.68/0.89    inference(subsumption_resolution,[],[f572,f159])).
% 3.68/0.89  fof(f572,plain,(
% 3.68/0.89    v2_struct_0(sK0) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_10 | spl8_25)),
% 3.68/0.89    inference(subsumption_resolution,[],[f571,f154])).
% 3.68/0.89  fof(f571,plain,(
% 3.68/0.89    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | spl8_25)),
% 3.68/0.89    inference(subsumption_resolution,[],[f570,f149])).
% 3.68/0.89  fof(f570,plain,(
% 3.68/0.89    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | spl8_25)),
% 3.68/0.89    inference(subsumption_resolution,[],[f569,f112])).
% 3.68/0.89  fof(f569,plain,(
% 3.68/0.89    ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | spl8_25)),
% 3.68/0.89    inference(subsumption_resolution,[],[f568,f136])).
% 3.68/0.89  fof(f568,plain,(
% 3.68/0.89    v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_25)),
% 3.68/0.89    inference(subsumption_resolution,[],[f567,f131])).
% 3.68/0.89  fof(f567,plain,(
% 3.68/0.89    ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_4 | spl8_25)),
% 3.68/0.89    inference(subsumption_resolution,[],[f566,f126])).
% 3.68/0.89  fof(f566,plain,(
% 3.68/0.89    ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_3 | spl8_25)),
% 3.68/0.89    inference(subsumption_resolution,[],[f564,f121])).
% 3.68/0.89  fof(f564,plain,(
% 3.68/0.89    ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_25),
% 3.68/0.89    inference(resolution,[],[f516,f86])).
% 3.68/0.89  fof(f86,plain,(
% 3.68/0.89    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.68/0.89    inference(cnf_transformation,[],[f52])).
% 3.68/0.89  fof(f516,plain,(
% 3.68/0.89    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | spl8_25),
% 3.68/0.89    inference(avatar_component_clause,[],[f514])).
% 3.68/0.89  fof(f293,plain,(
% 3.68/0.89    spl8_1 | spl8_13 | ~spl8_14 | ~spl8_15 | spl8_18 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12),
% 3.68/0.89    inference(avatar_split_clause,[],[f292,f163,f157,f152,f147,f143,f286,f211,f207,f203,f111])).
% 3.68/0.89  fof(f292,plain,(
% 3.68/0.89    v7_waybel_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | v1_compts_1(sK0) | (~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f291,f159])).
% 3.68/0.89  fof(f291,plain,(
% 3.68/0.89    v7_waybel_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | v1_compts_1(sK0) | v2_struct_0(sK0) | (~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f290,f154])).
% 3.68/0.89  fof(f290,plain,(
% 3.68/0.89    v7_waybel_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | v1_compts_1(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_8 | ~spl8_9 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f280,f149])).
% 3.68/0.89  fof(f280,plain,(
% 3.68/0.89    v7_waybel_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_8 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(resolution,[],[f226,f93])).
% 3.68/0.89  fof(f226,plain,(
% 3.68/0.89    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v7_waybel_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) ) | (~spl8_8 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f225,f159])).
% 3.68/0.89  fof(f225,plain,(
% 3.68/0.89    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl8_8 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f224,f165])).
% 3.68/0.89  fof(f224,plain,(
% 3.68/0.89    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl8_8),
% 3.68/0.89    inference(duplicate_literal_removal,[],[f223])).
% 3.68/0.89  fof(f223,plain,(
% 3.68/0.89    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0)) ) | ~spl8_8),
% 3.68/0.89    inference(resolution,[],[f79,f144])).
% 3.68/0.89  fof(f272,plain,(
% 3.68/0.89    spl8_1 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_13),
% 3.68/0.89    inference(avatar_contradiction_clause,[],[f271])).
% 3.68/0.89  fof(f271,plain,(
% 3.68/0.89    $false | (spl8_1 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_13)),
% 3.68/0.89    inference(subsumption_resolution,[],[f270,f159])).
% 3.68/0.89  fof(f270,plain,(
% 3.68/0.89    v2_struct_0(sK0) | (spl8_1 | ~spl8_9 | ~spl8_10 | ~spl8_13)),
% 3.68/0.89    inference(subsumption_resolution,[],[f269,f154])).
% 3.68/0.89  fof(f269,plain,(
% 3.68/0.89    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_9 | ~spl8_13)),
% 3.68/0.89    inference(subsumption_resolution,[],[f268,f149])).
% 3.68/0.89  fof(f268,plain,(
% 3.68/0.89    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_13)),
% 3.68/0.89    inference(subsumption_resolution,[],[f266,f113])).
% 3.68/0.89  fof(f266,plain,(
% 3.68/0.89    v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_13),
% 3.68/0.89    inference(resolution,[],[f205,f90])).
% 3.68/0.89  fof(f205,plain,(
% 3.68/0.89    v2_struct_0(sK5(sK0)) | ~spl8_13),
% 3.68/0.89    inference(avatar_component_clause,[],[f203])).
% 3.68/0.89  fof(f262,plain,(
% 3.68/0.89    spl8_13 | ~spl8_14 | ~spl8_15 | spl8_17 | spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12),
% 3.68/0.89    inference(avatar_split_clause,[],[f257,f163,f157,f152,f147,f143,f111,f259,f211,f207,f203])).
% 3.68/0.89  fof(f257,plain,(
% 3.68/0.89    v4_orders_2(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f256,f159])).
% 3.68/0.89  fof(f256,plain,(
% 3.68/0.89    v4_orders_2(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f255,f154])).
% 3.68/0.89  fof(f255,plain,(
% 3.68/0.89    v4_orders_2(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_8 | ~spl8_9 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f254,f149])).
% 3.68/0.89  fof(f254,plain,(
% 3.68/0.89    v4_orders_2(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_8 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f253,f113])).
% 3.68/0.89  fof(f253,plain,(
% 3.68/0.89    v4_orders_2(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_8 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(resolution,[],[f222,f93])).
% 3.68/0.89  fof(f222,plain,(
% 3.68/0.89    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v4_orders_2(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) ) | (~spl8_8 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f221,f159])).
% 3.68/0.89  fof(f221,plain,(
% 3.68/0.89    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl8_8 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f220,f165])).
% 3.68/0.89  fof(f220,plain,(
% 3.68/0.89    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl8_8),
% 3.68/0.89    inference(duplicate_literal_removal,[],[f219])).
% 3.68/0.89  fof(f219,plain,(
% 3.68/0.89    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0)) ) | ~spl8_8),
% 3.68/0.89    inference(resolution,[],[f78,f144])).
% 3.68/0.89  fof(f246,plain,(
% 3.68/0.89    spl8_1 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_15),
% 3.68/0.89    inference(avatar_contradiction_clause,[],[f245])).
% 3.68/0.89  fof(f245,plain,(
% 3.68/0.89    $false | (spl8_1 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_15)),
% 3.68/0.89    inference(subsumption_resolution,[],[f244,f159])).
% 3.68/0.89  fof(f244,plain,(
% 3.68/0.89    v2_struct_0(sK0) | (spl8_1 | ~spl8_9 | ~spl8_10 | spl8_15)),
% 3.68/0.89    inference(subsumption_resolution,[],[f243,f154])).
% 3.68/0.89  fof(f243,plain,(
% 3.68/0.89    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_9 | spl8_15)),
% 3.68/0.89    inference(subsumption_resolution,[],[f242,f149])).
% 3.68/0.89  fof(f242,plain,(
% 3.68/0.89    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_15)),
% 3.68/0.89    inference(subsumption_resolution,[],[f240,f113])).
% 3.68/0.89  fof(f240,plain,(
% 3.68/0.89    v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_15),
% 3.68/0.89    inference(resolution,[],[f213,f92])).
% 3.68/0.89  fof(f213,plain,(
% 3.68/0.89    ~v7_waybel_0(sK5(sK0)) | spl8_15),
% 3.68/0.89    inference(avatar_component_clause,[],[f211])).
% 3.68/0.89  fof(f234,plain,(
% 3.68/0.89    spl8_1 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_14),
% 3.68/0.89    inference(avatar_contradiction_clause,[],[f233])).
% 3.68/0.89  fof(f233,plain,(
% 3.68/0.89    $false | (spl8_1 | ~spl8_9 | ~spl8_10 | spl8_11 | spl8_14)),
% 3.68/0.89    inference(subsumption_resolution,[],[f232,f159])).
% 3.68/0.89  fof(f232,plain,(
% 3.68/0.89    v2_struct_0(sK0) | (spl8_1 | ~spl8_9 | ~spl8_10 | spl8_14)),
% 3.68/0.89    inference(subsumption_resolution,[],[f231,f154])).
% 3.68/0.89  fof(f231,plain,(
% 3.68/0.89    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_9 | spl8_14)),
% 3.68/0.89    inference(subsumption_resolution,[],[f230,f149])).
% 3.68/0.89  fof(f230,plain,(
% 3.68/0.89    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_14)),
% 3.68/0.89    inference(subsumption_resolution,[],[f228,f113])).
% 3.68/0.89  fof(f228,plain,(
% 3.68/0.89    v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_14),
% 3.68/0.89    inference(resolution,[],[f209,f91])).
% 3.68/0.89  fof(f209,plain,(
% 3.68/0.89    ~v4_orders_2(sK5(sK0)) | spl8_14),
% 3.68/0.89    inference(avatar_component_clause,[],[f207])).
% 3.68/0.89  fof(f218,plain,(
% 3.68/0.89    spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_16 | spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12),
% 3.68/0.89    inference(avatar_split_clause,[],[f201,f163,f157,f152,f147,f143,f111,f215,f211,f207,f203])).
% 3.68/0.89  fof(f201,plain,(
% 3.68/0.89    ~v2_struct_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f200,f159])).
% 3.68/0.89  fof(f200,plain,(
% 3.68/0.89    ~v2_struct_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f199,f154])).
% 3.68/0.89  fof(f199,plain,(
% 3.68/0.89    ~v2_struct_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_8 | ~spl8_9 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f198,f149])).
% 3.68/0.89  fof(f198,plain,(
% 3.68/0.89    ~v2_struct_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_8 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f197,f113])).
% 3.68/0.89  fof(f197,plain,(
% 3.68/0.89    ~v2_struct_0(sK2(sK5(sK0))) | ~v7_waybel_0(sK5(sK0)) | ~v4_orders_2(sK5(sK0)) | v2_struct_0(sK5(sK0)) | v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_8 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(resolution,[],[f196,f93])).
% 3.68/0.89  fof(f196,plain,(
% 3.68/0.89    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v2_struct_0(sK2(X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) ) | (~spl8_8 | spl8_11 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f195,f159])).
% 3.68/0.89  fof(f195,plain,(
% 3.68/0.89    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl8_8 | ~spl8_12)),
% 3.68/0.89    inference(subsumption_resolution,[],[f194,f165])).
% 3.68/0.89  fof(f194,plain,(
% 3.68/0.89    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl8_8),
% 3.68/0.89    inference(duplicate_literal_removal,[],[f193])).
% 3.68/0.89  fof(f193,plain,(
% 3.68/0.89    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0)) ) | ~spl8_8),
% 3.68/0.89    inference(resolution,[],[f77,f144])).
% 3.68/0.89  fof(f166,plain,(
% 3.68/0.89    spl8_12 | ~spl8_9),
% 3.68/0.89    inference(avatar_split_clause,[],[f161,f147,f163])).
% 3.68/0.89  fof(f161,plain,(
% 3.68/0.89    l1_struct_0(sK0) | ~spl8_9),
% 3.68/0.89    inference(resolution,[],[f96,f149])).
% 3.68/0.89  fof(f160,plain,(
% 3.68/0.89    ~spl8_11),
% 3.68/0.89    inference(avatar_split_clause,[],[f65,f157])).
% 3.68/0.89  fof(f65,plain,(
% 3.68/0.89    ~v2_struct_0(sK0)),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f47,plain,(
% 3.68/0.89    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.68/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).
% 3.68/0.89  fof(f44,plain,(
% 3.68/0.89    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.68/0.89    introduced(choice_axiom,[])).
% 3.68/0.89  fof(f45,plain,(
% 3.68/0.89    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 3.68/0.89    introduced(choice_axiom,[])).
% 3.68/0.89  fof(f46,plain,(
% 3.68/0.89    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 3.68/0.89    introduced(choice_axiom,[])).
% 3.68/0.89  fof(f43,plain,(
% 3.68/0.89    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.68/0.89    inference(rectify,[],[f42])).
% 3.68/0.89  fof(f42,plain,(
% 3.68/0.89    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.68/0.89    inference(flattening,[],[f41])).
% 3.68/0.89  fof(f41,plain,(
% 3.68/0.89    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.68/0.89    inference(nnf_transformation,[],[f19])).
% 3.68/0.89  fof(f19,plain,(
% 3.68/0.89    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.68/0.89    inference(flattening,[],[f18])).
% 3.68/0.89  fof(f18,plain,(
% 3.68/0.89    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.68/0.89    inference(ennf_transformation,[],[f17])).
% 3.68/0.89  fof(f17,negated_conjecture,(
% 3.68/0.89    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.68/0.89    inference(negated_conjecture,[],[f16])).
% 3.68/0.89  fof(f16,conjecture,(
% 3.68/0.89    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.68/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).
% 3.68/0.89  fof(f155,plain,(
% 3.68/0.89    spl8_10),
% 3.68/0.89    inference(avatar_split_clause,[],[f66,f152])).
% 3.68/0.89  fof(f66,plain,(
% 3.68/0.89    v2_pre_topc(sK0)),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f150,plain,(
% 3.68/0.89    spl8_9),
% 3.68/0.89    inference(avatar_split_clause,[],[f67,f147])).
% 3.68/0.89  fof(f67,plain,(
% 3.68/0.89    l1_pre_topc(sK0)),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f145,plain,(
% 3.68/0.89    spl8_1 | spl8_8),
% 3.68/0.89    inference(avatar_split_clause,[],[f68,f143,f111])).
% 3.68/0.89  fof(f68,plain,(
% 3.68/0.89    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f141,plain,(
% 3.68/0.89    spl8_1 | spl8_7),
% 3.68/0.89    inference(avatar_split_clause,[],[f69,f139,f111])).
% 3.68/0.89  fof(f69,plain,(
% 3.68/0.89    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f137,plain,(
% 3.68/0.89    ~spl8_1 | ~spl8_6),
% 3.68/0.89    inference(avatar_split_clause,[],[f70,f134,f111])).
% 3.68/0.89  fof(f70,plain,(
% 3.68/0.89    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f132,plain,(
% 3.68/0.89    ~spl8_1 | spl8_5),
% 3.68/0.89    inference(avatar_split_clause,[],[f71,f129,f111])).
% 3.68/0.89  fof(f71,plain,(
% 3.68/0.89    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f127,plain,(
% 3.68/0.89    ~spl8_1 | spl8_4),
% 3.68/0.89    inference(avatar_split_clause,[],[f72,f124,f111])).
% 3.68/0.89  fof(f72,plain,(
% 3.68/0.89    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f122,plain,(
% 3.68/0.89    ~spl8_1 | spl8_3),
% 3.68/0.89    inference(avatar_split_clause,[],[f73,f119,f111])).
% 3.68/0.89  fof(f73,plain,(
% 3.68/0.89    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  fof(f117,plain,(
% 3.68/0.89    ~spl8_1 | spl8_2),
% 3.68/0.89    inference(avatar_split_clause,[],[f74,f115,f111])).
% 3.68/0.89  fof(f74,plain,(
% 3.68/0.89    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~v1_compts_1(sK0)) )),
% 3.68/0.89    inference(cnf_transformation,[],[f47])).
% 3.68/0.89  % SZS output end Proof for theBenchmark
% 3.68/0.89  % (4172)------------------------------
% 3.68/0.89  % (4172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.89  % (4172)Termination reason: Refutation
% 3.68/0.89  
% 3.68/0.89  % (4172)Memory used [KB]: 8187
% 3.68/0.89  % (4172)Time elapsed: 0.230 s
% 3.68/0.89  % (4172)------------------------------
% 3.68/0.89  % (4172)------------------------------
% 3.68/0.89  % (4139)Success in time 0.512 s
%------------------------------------------------------------------------------
