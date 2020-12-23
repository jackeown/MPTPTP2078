%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1992+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:01 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  280 ( 523 expanded)
%              Number of leaves         :   72 ( 244 expanded)
%              Depth                    :   12
%              Number of atoms          : 1328 (3099 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1796,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f158,f166,f170,f174,f178,f182,f186,f190,f194,f198,f202,f206,f753,f755,f758,f1227,f1233,f1236,f1339,f1344,f1350,f1356,f1363,f1373,f1471,f1489,f1512,f1526,f1542,f1545,f1639,f1654,f1708,f1710,f1727,f1735,f1746,f1763,f1785,f1790,f1795])).

fof(f1795,plain,
    ( o_0_0_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1790,plain,
    ( spl6_72
    | ~ spl6_4
    | ~ spl6_14
    | spl6_124 ),
    inference(avatar_split_clause,[],[f1786,f1783,f204,f164,f1316])).

fof(f1316,plain,
    ( spl6_72
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f164,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f204,plain,
    ( spl6_14
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1783,plain,
    ( spl6_124
  <=> m1_subset_1(sK4(sK1,o_0_0_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f1786,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_14
    | spl6_124 ),
    inference(resolution,[],[f1784,f218])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(X0,o_0_0_xboole_0),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_14 ),
    inference(resolution,[],[f217,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f217,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0,o_0_0_xboole_0),X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_14 ),
    inference(resolution,[],[f215,f205])).

fof(f205,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f204])).

fof(f215,plain,(
    ! [X10,X9] :
      ( ~ v1_xboole_0(X10)
      | r2_hidden(sK4(X9,X10),X9)
      | X9 = X10 ) ),
    inference(resolution,[],[f140,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f140,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f90,f91])).

fof(f91,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f1784,plain,
    ( ~ m1_subset_1(sK4(sK1,o_0_0_xboole_0),u1_struct_0(sK0))
    | spl6_124 ),
    inference(avatar_component_clause,[],[f1783])).

fof(f1785,plain,
    ( spl6_72
    | ~ spl6_124
    | ~ spl6_14
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1770,f1761,f204,f1783,f1316])).

fof(f1761,plain,
    ( spl6_121
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f1770,plain,
    ( ~ m1_subset_1(sK4(sK1,o_0_0_xboole_0),u1_struct_0(sK0))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_14
    | ~ spl6_121 ),
    inference(resolution,[],[f1762,f217])).

fof(f1762,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f1761])).

fof(f1763,plain,
    ( spl6_36
    | ~ spl6_11
    | ~ spl6_55
    | ~ spl6_7
    | spl6_121
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f1759,f1337,f1761,f176,f1222,f192,f747])).

fof(f747,plain,
    ( spl6_36
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f192,plain,
    ( spl6_11
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f1222,plain,
    ( spl6_55
  <=> v2_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f176,plain,
    ( spl6_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1337,plain,
    ( spl6_74
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,k4_yellow_0(sK0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f1759,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_74 ),
    inference(duplicate_literal_removal,[],[f1756])).

fof(f1756,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_74 ),
    inference(resolution,[],[f1338,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

fof(f1338,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,k4_yellow_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f1337])).

fof(f1746,plain,
    ( spl6_36
    | ~ spl6_11
    | ~ spl6_55
    | ~ spl6_7
    | ~ spl6_116
    | ~ spl6_117 ),
    inference(avatar_split_clause,[],[f1736,f1722,f1706,f176,f1222,f192,f747])).

fof(f1706,plain,
    ( spl6_116
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f1722,plain,
    ( spl6_117
  <=> v1_xboole_0(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f1736,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v2_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_117 ),
    inference(resolution,[],[f1723,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k12_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_waybel_0)).

fof(f1723,plain,
    ( v1_xboole_0(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))))
    | ~ spl6_117 ),
    inference(avatar_component_clause,[],[f1722])).

fof(f1735,plain,
    ( spl6_36
    | ~ spl6_7
    | ~ spl6_116
    | spl6_118 ),
    inference(avatar_split_clause,[],[f1734,f1725,f1706,f176,f747])).

fof(f1725,plain,
    ( spl6_118
  <=> m1_subset_1(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f1734,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl6_118 ),
    inference(resolution,[],[f1726,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_waybel_0)).

fof(f1726,plain,
    ( ~ m1_subset_1(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_118 ),
    inference(avatar_component_clause,[],[f1725])).

fof(f1727,plain,
    ( spl6_36
    | ~ spl6_13
    | ~ spl6_7
    | spl6_117
    | ~ spl6_118
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f1711,f546,f1725,f1722,f176,f200,f747])).

fof(f200,plain,
    ( spl6_13
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f546,plain,
    ( spl6_28
  <=> v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1711,plain,
    ( ~ m1_subset_1(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28 ),
    inference(resolution,[],[f547,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_waybel_0)).

fof(f547,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f546])).

fof(f1710,plain,
    ( ~ spl6_33
    | spl6_116 ),
    inference(avatar_split_clause,[],[f1709,f1706,f734])).

fof(f734,plain,
    ( spl6_33
  <=> m1_subset_1(k5_waybel_0(sK0,k4_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1709,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK0,k4_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_116 ),
    inference(resolution,[],[f1707,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1707,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_116 ),
    inference(avatar_component_clause,[],[f1706])).

fof(f1708,plain,
    ( spl6_28
    | ~ spl6_116
    | ~ spl6_80
    | spl6_115 ),
    inference(avatar_split_clause,[],[f1704,f1652,f1371,f1706,f546])).

fof(f1371,plain,
    ( spl6_80
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f1652,plain,
    ( spl6_115
  <=> r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f1704,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))))
    | ~ spl6_80
    | spl6_115 ),
    inference(resolution,[],[f1653,f1372])).

fof(f1372,plain,
    ( ! [X0] :
        ( r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,X0))) )
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f1371])).

fof(f1653,plain,
    ( ~ r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))))
    | spl6_115 ),
    inference(avatar_component_clause,[],[f1652])).

fof(f1654,plain,
    ( ~ spl6_115
    | spl6_28
    | ~ spl6_2
    | ~ spl6_113 ),
    inference(avatar_split_clause,[],[f1648,f1637,f156,f546,f1652])).

fof(f156,plain,
    ( spl6_2
  <=> r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1637,plain,
    ( spl6_113
  <=> ! [X0] :
        ( ~ r2_hidden(k4_yellow_0(sK0),X0)
        | v1_xboole_0(X0)
        | ~ r2_subset_1(X0,k1_waybel_3(sK0,k4_yellow_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f1648,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))))
    | ~ r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))))
    | ~ spl6_2
    | ~ spl6_113 ),
    inference(resolution,[],[f1638,f157])).

fof(f157,plain,
    ( r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f156])).

fof(f1638,plain,
    ( ! [X0] :
        ( ~ r2_subset_1(X0,k1_waybel_3(sK0,k4_yellow_0(sK0)))
        | v1_xboole_0(X0)
        | ~ r2_hidden(k4_yellow_0(sK0),X0) )
    | ~ spl6_113 ),
    inference(avatar_component_clause,[],[f1637])).

fof(f1639,plain,
    ( spl6_29
    | spl6_113
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f1633,f1540,f1637,f549])).

fof(f549,plain,
    ( spl6_29
  <=> v1_xboole_0(k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f1540,plain,
    ( spl6_100
  <=> r2_hidden(k4_yellow_0(sK0),k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f1633,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_yellow_0(sK0),X0)
        | ~ r2_subset_1(X0,k1_waybel_3(sK0,k4_yellow_0(sK0)))
        | v1_xboole_0(k1_waybel_3(sK0,k4_yellow_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl6_100 ),
    inference(resolution,[],[f1562,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r2_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( ( r2_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r2_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_subset_1)).

fof(f1562,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(X3,k1_waybel_3(sK0,k4_yellow_0(sK0)))
        | ~ r2_hidden(k4_yellow_0(sK0),X3) )
    | ~ spl6_100 ),
    inference(resolution,[],[f1541,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f87])).

fof(f87,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1541,plain,
    ( r2_hidden(k4_yellow_0(sK0),k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f1545,plain,
    ( spl6_36
    | ~ spl6_13
    | ~ spl6_7
    | ~ spl6_37
    | ~ spl6_29
    | spl6_98 ),
    inference(avatar_split_clause,[],[f1543,f1524,f549,f751,f176,f200,f747])).

fof(f751,plain,
    ( spl6_37
  <=> m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f1524,plain,
    ( spl6_98
  <=> v1_xboole_0(a_2_0_waybel_3(sK0,k4_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f1543,plain,
    ( ~ v1_xboole_0(k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl6_98 ),
    inference(superposition,[],[f1525,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_3)).

fof(f1525,plain,
    ( ~ v1_xboole_0(a_2_0_waybel_3(sK0,k4_yellow_0(sK0)))
    | spl6_98 ),
    inference(avatar_component_clause,[],[f1524])).

fof(f1542,plain,
    ( spl6_36
    | ~ spl6_13
    | ~ spl6_7
    | ~ spl6_37
    | spl6_100
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f1522,f1510,f1540,f751,f176,f200,f747])).

fof(f1510,plain,
    ( spl6_96
  <=> r2_hidden(k4_yellow_0(sK0),a_2_0_waybel_3(sK0,k4_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f1522,plain,
    ( r2_hidden(k4_yellow_0(sK0),k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_96 ),
    inference(superposition,[],[f1511,f122])).

fof(f1511,plain,
    ( r2_hidden(k4_yellow_0(sK0),a_2_0_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f1510])).

fof(f1526,plain,
    ( ~ spl6_98
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f1521,f1510,f1524])).

fof(f1521,plain,
    ( ~ v1_xboole_0(a_2_0_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ spl6_96 ),
    inference(resolution,[],[f1511,f142])).

fof(f1512,plain,
    ( spl6_96
    | ~ spl6_37
    | ~ spl6_6
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f1506,f1487,f172,f751,f1510])).

fof(f172,plain,
    ( spl6_6
  <=> v1_waybel_3(k4_yellow_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1487,plain,
    ( spl6_92
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v1_waybel_3(X4,sK0)
        | r2_hidden(X4,a_2_0_waybel_3(sK0,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f1506,plain,
    ( ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | r2_hidden(k4_yellow_0(sK0),a_2_0_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ spl6_6
    | ~ spl6_92 ),
    inference(resolution,[],[f1488,f173])).

fof(f173,plain,
    ( v1_waybel_3(k4_yellow_0(sK0),sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1488,plain,
    ( ! [X4] :
        ( ~ v1_waybel_3(X4,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(X4,a_2_0_waybel_3(sK0,X4)) )
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f1487])).

fof(f1489,plain,
    ( spl6_36
    | ~ spl6_13
    | ~ spl6_7
    | spl6_92
    | ~ spl6_89 ),
    inference(avatar_split_clause,[],[f1476,f1469,f1487,f176,f200,f747])).

fof(f1469,plain,
    ( spl6_89
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_3(sK0,X0,X1)
        | r2_hidden(X0,a_2_0_waybel_3(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f1476,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(X4,a_2_0_waybel_3(sK0,X4))
        | ~ v1_waybel_3(X4,sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_89 ),
    inference(duplicate_literal_removal,[],[f1475])).

fof(f1475,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(X4,a_2_0_waybel_3(sK0,X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v1_waybel_3(X4,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_89 ),
    inference(resolution,[],[f1470,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_waybel_3(X0,X1,X1)
      | ~ v1_waybel_3(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_3(X1,X0)
              | ~ r1_waybel_3(X0,X1,X1) )
            & ( r1_waybel_3(X0,X1,X1)
              | ~ v1_waybel_3(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_3)).

fof(f1470,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,a_2_0_waybel_3(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f1469])).

fof(f1471,plain,
    ( ~ spl6_13
    | ~ spl6_7
    | spl6_89
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f1467,f184,f1469,f176,f200])).

fof(f184,plain,
    ( spl6_9
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1467,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | r2_hidden(X0,a_2_0_waybel_3(sK0,X1))
        | ~ r1_waybel_3(sK0,X0,X1) )
    | ~ spl6_9 ),
    inference(resolution,[],[f1050,f185])).

fof(f185,plain,
    ( v2_lattice3(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f184])).

fof(f1050,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | r2_hidden(X1,a_2_0_waybel_3(X0,X2))
      | ~ r1_waybel_3(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f1049])).

fof(f1049,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | r2_hidden(X1,a_2_0_waybel_3(X0,X2))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f151,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f151,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ r1_waybel_3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | r2_hidden(X3,a_2_0_waybel_3(X1,X2)) ) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      | ~ r1_waybel_3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r1_waybel_3(X1,sK5(X0,X1,X2),X2)
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f95,f96])).

fof(f96,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r1_waybel_3(X1,sK5(X0,X1,X2),X2)
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r1_waybel_3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r1_waybel_3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_waybel_3)).

fof(f1373,plain,
    ( spl6_36
    | ~ spl6_7
    | spl6_80
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f1369,f1361,f1371,f176,f747])).

fof(f1361,plain,
    ( spl6_78
  <=> ! [X0] :
        ( ~ m1_subset_1(k12_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1369,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_78 ),
    inference(duplicate_literal_removal,[],[f1368])).

fof(f1368,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_78 ),
    inference(resolution,[],[f1362,f135])).

fof(f1362,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k12_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,X0))) )
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f1361])).

fof(f1363,plain,
    ( ~ spl6_13
    | ~ spl6_12
    | ~ spl6_11
    | ~ spl6_9
    | ~ spl6_7
    | spl6_78
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f1357,f1354,f1361,f176,f184,f192,f196,f200])).

fof(f196,plain,
    ( spl6_12
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f1354,plain,
    ( spl6_77
  <=> ! [X0] :
        ( ~ v2_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | v1_xboole_0(k4_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f1357,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k12_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_77 ),
    inference(resolution,[],[f1355,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v2_waybel_0(k12_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_waybel_0)).

fof(f1355,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | v1_xboole_0(k4_waybel_0(sK0,X0)) )
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f1354])).

fof(f1356,plain,
    ( ~ spl6_7
    | spl6_77
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f1352,f1348,f1354,f176])).

fof(f1348,plain,
    ( spl6_76
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_waybel_0(X0,sK0)
        | v1_xboole_0(k4_waybel_0(sK0,X0))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | ~ m1_subset_1(k4_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f1352,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(X0,sK0)
        | v1_xboole_0(k4_waybel_0(sK0,X0))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl6_76 ),
    inference(duplicate_literal_removal,[],[f1351])).

fof(f1351,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(X0,sK0)
        | v1_xboole_0(k4_waybel_0(sK0,X0))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl6_76 ),
    inference(resolution,[],[f1349,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(f1349,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_waybel_0(X0,sK0)
        | v1_xboole_0(k4_waybel_0(sK0,X0))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f1348])).

fof(f1350,plain,
    ( spl6_36
    | ~ spl6_13
    | ~ spl6_12
    | ~ spl6_7
    | spl6_76
    | ~ spl6_75 ),
    inference(avatar_split_clause,[],[f1346,f1342,f1348,f176,f196,f200,f747])).

fof(f1342,plain,
    ( spl6_75
  <=> ! [X0] :
        ( r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k4_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_waybel_0(k4_waybel_0(sK0,X0),sK0)
        | v1_xboole_0(k4_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f1346,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k4_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | v1_xboole_0(k4_waybel_0(sK0,X0))
        | ~ v2_waybel_0(X0,sK0)
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_75 ),
    inference(duplicate_literal_removal,[],[f1345])).

fof(f1345,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k4_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | v1_xboole_0(k4_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_waybel_0(X0,sK0)
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_75 ),
    inference(resolution,[],[f1343,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

% (26047)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% (26048)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
fof(f64,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_0(X1,X0)
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v2_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_waybel_0)).

fof(f1343,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(k4_waybel_0(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k4_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | v1_xboole_0(k4_waybel_0(sK0,X0)) )
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1344,plain,
    ( spl6_36
    | ~ spl6_12
    | ~ spl6_7
    | spl6_75
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f1340,f1225,f1342,f176,f196,f747])).

fof(f1225,plain,
    ( spl6_56
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_yellow_0(sK0),X0)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,sK0)
        | ~ v13_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f1340,plain,
    ( ! [X0] :
        ( r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,X0))
        | v1_xboole_0(k4_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k4_waybel_0(sK0,X0),sK0)
        | ~ m1_subset_1(k4_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_56 ),
    inference(resolution,[],[f1226,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_waybel_0)).

fof(f1226,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(X0,sK0)
        | r2_hidden(k4_yellow_0(sK0),X0)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f1339,plain,
    ( spl6_36
    | ~ spl6_13
    | ~ spl6_7
    | ~ spl6_37
    | spl6_74
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f1335,f153,f1337,f751,f176,f200,f747])).

fof(f153,plain,
    ( spl6_1
  <=> ! [X2] :
        ( ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1335,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,k4_yellow_0(sK0))
        | ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f1334])).

fof(f1334,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,k4_yellow_0(sK0))
        | ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f154,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f154,plain,
    ( ! [X2] :
        ( ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f153])).

fof(f1236,plain,
    ( ~ spl6_7
    | spl6_36
    | ~ spl6_13
    | ~ spl6_8
    | spl6_57 ),
    inference(avatar_split_clause,[],[f1234,f1231,f180,f200,f747,f176])).

fof(f180,plain,
    ( spl6_8
  <=> v3_waybel_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1231,plain,
    ( spl6_57
  <=> v24_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f1234,plain,
    ( ~ v3_waybel_3(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | spl6_57 ),
    inference(resolution,[],[f1232,f115])).

fof(f115,plain,(
    ! [X0] :
      ( v24_waybel_0(X0)
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_3(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_waybel_3)).

fof(f1232,plain,
    ( ~ v24_waybel_0(sK0)
    | spl6_57 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1233,plain,
    ( ~ spl6_7
    | ~ spl6_13
    | ~ spl6_10
    | ~ spl6_57
    | spl6_55 ),
    inference(avatar_split_clause,[],[f1228,f1222,f1231,f188,f200,f176])).

fof(f188,plain,
    ( spl6_10
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1228,plain,
    ( ~ v24_waybel_0(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl6_55 ),
    inference(resolution,[],[f1223,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v24_waybel_0(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) )
       => ( v2_yellow_0(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_waybel_0)).

fof(f1223,plain,
    ( ~ v2_yellow_0(sK0)
    | spl6_55 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f1227,plain,
    ( spl6_36
    | ~ spl6_13
    | ~ spl6_12
    | ~ spl6_55
    | ~ spl6_7
    | spl6_56
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f1218,f192,f1225,f176,f1222,f196,f200,f747])).

fof(f1218,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(X0,sK0)
        | ~ v2_waybel_0(X0,sK0)
        | v1_xboole_0(X0)
        | ~ l1_orders_2(sK0)
        | ~ v2_yellow_0(sK0)
        | r2_hidden(k4_yellow_0(sK0),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11 ),
    inference(resolution,[],[f121,f193])).

fof(f193,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f192])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | r2_hidden(k4_yellow_0(X0),X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_4)).

fof(f758,plain,
    ( ~ spl6_7
    | ~ spl6_9
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f756,f747,f184,f176])).

fof(f756,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_36 ),
    inference(resolution,[],[f748,f112])).

fof(f748,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f747])).

fof(f755,plain,
    ( ~ spl6_7
    | spl6_37 ),
    inference(avatar_split_clause,[],[f754,f751,f176])).

fof(f754,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_37 ),
    inference(resolution,[],[f752,f111])).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_0)).

fof(f752,plain,
    ( ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f751])).

fof(f753,plain,
    ( spl6_36
    | ~ spl6_7
    | ~ spl6_37
    | spl6_33 ),
    inference(avatar_split_clause,[],[f745,f734,f751,f176,f747])).

fof(f745,plain,
    ( ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl6_33 ),
    inference(resolution,[],[f735,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f735,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK0,k4_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_33 ),
    inference(avatar_component_clause,[],[f734])).

fof(f206,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f110,f204])).

fof(f110,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f202,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f98,f200])).

fof(f98,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( ( r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
      | ( ! [X2] :
            ( ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
            | ~ r2_hidden(X2,sK1)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & r1_waybel_3(sK0,k2_yellow_0(sK0,sK1),k4_yellow_0(sK0))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(sK1) ) )
    & v1_waybel_3(k4_yellow_0(sK0),sK0)
    & l1_orders_2(sK0)
    & v3_waybel_3(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f82,f81])).

fof(f81,plain,
    ( ? [X0] :
        ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) ) )
        & v1_waybel_3(k4_yellow_0(X0),X0)
        & l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ( r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
            & r1_waybel_3(sK0,k2_yellow_0(sK0,X1),k4_yellow_0(sK0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(sK0),sK0)
      & l1_orders_2(sK0)
      & v3_waybel_3(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & r1_waybel_3(sK0,k2_yellow_0(sK0,X1),k4_yellow_0(sK0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
          | ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & r1_waybel_3(sK0,k2_yellow_0(sK0,sK1),k4_yellow_0(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v1_waybel_3(k4_yellow_0(X0),X0)
         => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
            & ! [X1] :
                ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X1) )
               => ~ ( ! [X2] :
                        ( m1_subset_1(X2,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                            & r2_hidden(X2,X1) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v1_waybel_3(k4_yellow_0(X0),X0)
         => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
            & ! [X1] :
                ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X1)
                  & ~ v1_xboole_0(X1) )
               => ~ ( ! [X2] :
                        ( m1_subset_1(X2,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                            & r2_hidden(X2,X1) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v1_waybel_3(k4_yellow_0(X0),X0)
       => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
          & ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_finset_1(X1)
                & ~ v1_xboole_0(X1) )
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,u1_struct_0(X0))
                     => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                          & r2_hidden(X2,X1) ) )
                  & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_waybel_7)).

fof(f198,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f99,f196])).

fof(f99,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f194,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f100,f192])).

fof(f100,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f190,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f101,f188])).

fof(f101,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f186,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f102,f184])).

fof(f102,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f182,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f103,f180])).

fof(f103,plain,(
    v3_waybel_3(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f178,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f104,f176])).

fof(f104,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f174,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f105,f172])).

fof(f105,plain,(
    v1_waybel_3(k4_yellow_0(sK0),sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f170,plain,
    ( ~ spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f106,f156,f168])).

fof(f168,plain,
    ( spl6_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f106,plain,
    ( r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f166,plain,
    ( spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f107,f156,f164])).

fof(f107,plain,
    ( r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f83])).

fof(f158,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f109,f156,f153])).

fof(f109,plain,(
    ! [X2] :
      ( r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
      | ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f83])).

%------------------------------------------------------------------------------
