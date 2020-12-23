%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:18 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 468 expanded)
%              Number of leaves         :   43 ( 205 expanded)
%              Depth                    :   11
%              Number of atoms          :  987 (2636 expanded)
%              Number of equality atoms :   61 (  86 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f123,f128,f133,f138,f143,f148,f153,f162,f164,f292,f307,f311,f323,f332,f355,f376,f395,f405,f416,f619,f984,f1003,f1018,f1049,f1061,f1090,f1108])).

fof(f1108,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_76 ),
    inference(avatar_contradiction_clause,[],[f1103])).

fof(f1103,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_76 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f137,f463,f1089,f152,f1089,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

fof(f152,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_8
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1089,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1087,plain,
    ( spl6_76
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f463,plain,(
    ! [X4] : r1_xboole_0(k1_xboole_0,X4) ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X4) ) ),
    inference(superposition,[],[f98,f457])).

fof(f457,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7) ),
    inference(resolution,[],[f371,f166])).

fof(f166,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f102,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f371,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,k2_xboole_0(X10,k1_xboole_0))
      | k1_xboole_0 = k4_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f191,f166])).

fof(f191,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X7,k4_xboole_0(X5,X6))
      | ~ r1_tarski(X5,k2_xboole_0(X6,X7))
      | k4_xboole_0(X5,X6) = X7 ) ),
    inference(resolution,[],[f105,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f137,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f132,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f127,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f122,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f117,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1090,plain,
    ( spl6_76
    | ~ spl6_6
    | ~ spl6_27
    | ~ spl6_35
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f1074,f1058,f413,f374,f140,f1087])).

fof(f140,plain,
    ( spl6_6
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f374,plain,
    ( spl6_27
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f413,plain,
    ( spl6_35
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1058,plain,
    ( spl6_74
  <=> m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f1074,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_6
    | ~ spl6_27
    | ~ spl6_35
    | ~ spl6_74 ),
    inference(backward_demodulation,[],[f142,f1073])).

fof(f1073,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_27
    | ~ spl6_35
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f1072,f1060])).

fof(f1060,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f1072,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2)
    | ~ spl6_27
    | ~ spl6_35
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f1068,f415])).

fof(f415,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f413])).

fof(f1068,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_2(sK2,sK0,sK2)
    | ~ spl6_27
    | ~ spl6_74 ),
    inference(resolution,[],[f1060,f375])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X1,sK0,X0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,X1) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f374])).

fof(f142,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f1061,plain,
    ( spl6_74
    | ~ spl6_10
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f1055,f329,f159,f1058])).

fof(f159,plain,
    ( spl6_10
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f329,plain,
    ( spl6_22
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1055,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl6_10
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f161,f331])).

fof(f331,plain,
    ( sK2 = sK3
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f329])).

fof(f161,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f1049,plain,
    ( ~ spl6_9
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f1048])).

fof(f1048,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1025,f85])).

fof(f85,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f1025,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl6_9
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f157,f331])).

fof(f157,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_9
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1018,plain,
    ( ~ spl6_17
    | spl6_25
    | ~ spl6_35
    | ~ spl6_73 ),
    inference(avatar_contradiction_clause,[],[f1017])).

fof(f1017,plain,
    ( $false
    | ~ spl6_17
    | spl6_25
    | ~ spl6_35
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f1016,f354])).

fof(f354,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl6_25
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1016,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f1013,f415])).

fof(f1013,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2)
    | ~ spl6_17
    | ~ spl6_73 ),
    inference(resolution,[],[f1002,f291])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1002,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1000,plain,
    ( spl6_73
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f1003,plain,
    ( spl6_73
    | spl6_22
    | ~ spl6_7
    | spl6_10
    | ~ spl6_70 ),
    inference(avatar_split_clause,[],[f998,f982,f159,f145,f329,f1000])).

fof(f145,plain,
    ( spl6_7
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f982,plain,
    ( spl6_70
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f998,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | ~ spl6_7
    | spl6_10
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f996,f160])).

fof(f160,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f996,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | ~ spl6_7
    | ~ spl6_70 ),
    inference(resolution,[],[f983,f147])).

fof(f147,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f145])).

fof(f983,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) )
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f982])).

fof(f984,plain,
    ( spl6_70
    | ~ spl6_6
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f620,f611,f140,f982])).

fof(f611,plain,
    ( spl6_42
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f620,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) )
    | ~ spl6_6
    | ~ spl6_42 ),
    inference(resolution,[],[f612,f142])).

fof(f612,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | X0 = X1
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f611])).

fof(f619,plain,
    ( spl6_42
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f584,f393,f150,f611])).

fof(f393,plain,
    ( spl6_31
  <=> ! [X1,X0,X2] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f584,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(resolution,[],[f394,f152])).

fof(f394,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f393])).

fof(f416,plain,
    ( spl6_35
    | ~ spl6_6
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f410,f403,f140,f413])).

fof(f403,plain,
    ( spl6_33
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f410,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6
    | ~ spl6_33 ),
    inference(resolution,[],[f404,f142])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f403])).

fof(f405,plain,
    ( spl6_33
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f350,f321,f150,f403])).

fof(f321,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(resolution,[],[f322,f152])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f321])).

fof(f395,plain,
    ( spl6_31
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f264,f135,f130,f125,f120,f115,f393])).

fof(f264,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f263,f117])).

fof(f263,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f262,f122])).

fof(f262,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f261,f127])).

fof(f261,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f260,f132])).

fof(f260,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f79,f137])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_orders_2(X2,X0,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

fof(f376,plain,
    ( spl6_27
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f253,f135,f130,f125,f120,f115,f374])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f252,f117])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f251,f122])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f250,f127])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f249,f132])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f243,f137])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f81,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f355,plain,
    ( ~ spl6_25
    | spl6_22
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f333,f155,f329,f352])).

fof(f333,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f157,f178])).

fof(f178,plain,(
    ! [X4,X3] :
      ( ~ r2_xboole_0(X4,X3)
      | X3 = X4
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f96,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f332,plain,
    ( spl6_22
    | spl6_9
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f319,f300,f155,f329])).

fof(f300,plain,
    ( spl6_19
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f319,plain,
    ( sK2 = sK3
    | spl6_9
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f317,f156])).

fof(f156,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f317,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl6_19 ),
    inference(resolution,[],[f302,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f302,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f300])).

fof(f323,plain,
    ( spl6_21
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f231,f135,f130,f125,f120,f115,f321])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f230,f117])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f229,f122])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f228,f127])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f227,f132])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f92,f137])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f311,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | spl6_20 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | spl6_20 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f137,f147,f152,f306,f92])).

fof(f306,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl6_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f307,plain,
    ( spl6_19
    | ~ spl6_20
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f298,f290,f159,f304,f300])).

fof(f298,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3)
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(resolution,[],[f291,f161])).

fof(f292,plain,
    ( spl6_17
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f214,f135,f130,f125,f120,f115,f290])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f213,f117])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f212,f122])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f211,f127])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f210,f132])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f80,f137])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X2,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f164,plain,
    ( ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f163,f159,f155])).

fof(f163,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f74,f161])).

fof(f74,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f53,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

fof(f162,plain,
    ( spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f73,f159,f155])).

fof(f73,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f153,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f70,f150])).

fof(f70,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f148,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f72,f145])).

fof(f72,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f143,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f71,f140])).

fof(f71,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f138,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f69,f135])).

fof(f69,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f133,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f68,f130])).

fof(f68,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f128,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f67,f125])).

fof(f67,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f123,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f66,f120])).

fof(f66,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f118,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f65,f115])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 18:08:51 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.21/0.50  % (6252)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (6243)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (6238)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (6237)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (6244)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (6240)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (6239)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (6253)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (6260)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (6247)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (6259)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (6236)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (6236)Refutation not found, incomplete strategy% (6236)------------------------------
% 0.21/0.53  % (6236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6236)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6236)Memory used [KB]: 10618
% 0.21/0.53  % (6236)Time elapsed: 0.114 s
% 0.21/0.53  % (6236)------------------------------
% 0.21/0.53  % (6236)------------------------------
% 0.21/0.53  % (6245)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.30/0.53  % (6258)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.30/0.53  % (6255)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.30/0.53  % (6249)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.30/0.53  % (6247)Refutation not found, incomplete strategy% (6247)------------------------------
% 1.30/0.53  % (6247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (6251)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.30/0.54  % (6246)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.30/0.54  % (6241)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.30/0.54  % (6248)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.30/0.54  % (6241)Refutation not found, incomplete strategy% (6241)------------------------------
% 1.30/0.54  % (6241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (6241)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (6241)Memory used [KB]: 6140
% 1.30/0.54  % (6241)Time elapsed: 0.122 s
% 1.30/0.54  % (6241)------------------------------
% 1.30/0.54  % (6241)------------------------------
% 1.30/0.54  % (6247)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (6247)Memory used [KB]: 10874
% 1.30/0.54  % (6247)Time elapsed: 0.112 s
% 1.30/0.54  % (6247)------------------------------
% 1.30/0.54  % (6247)------------------------------
% 1.30/0.54  % (6250)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.46/0.55  % (6254)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.46/0.55  % (6257)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.46/0.55  % (6242)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.46/0.55  % (6242)Refutation not found, incomplete strategy% (6242)------------------------------
% 1.46/0.55  % (6242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (6242)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (6242)Memory used [KB]: 10618
% 1.46/0.55  % (6242)Time elapsed: 0.136 s
% 1.46/0.55  % (6242)------------------------------
% 1.46/0.55  % (6242)------------------------------
% 1.46/0.55  % (6256)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.46/0.55  % (6261)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.46/0.56  % (6237)Refutation not found, incomplete strategy% (6237)------------------------------
% 1.46/0.56  % (6237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (6237)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (6237)Memory used [KB]: 10874
% 1.46/0.56  % (6237)Time elapsed: 0.130 s
% 1.46/0.56  % (6237)------------------------------
% 1.46/0.56  % (6237)------------------------------
% 1.46/0.56  % (6238)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f1109,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(avatar_sat_refutation,[],[f118,f123,f128,f133,f138,f143,f148,f153,f162,f164,f292,f307,f311,f323,f332,f355,f376,f395,f405,f416,f619,f984,f1003,f1018,f1049,f1061,f1090,f1108])).
% 1.46/0.56  fof(f1108,plain,(
% 1.46/0.56    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_76),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1103])).
% 1.46/0.56  fof(f1103,plain,(
% 1.46/0.56    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_76)),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f137,f463,f1089,f152,f1089,f77])).
% 1.46/0.56  fof(f77,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f20])).
% 1.46/0.56  fof(f20,axiom,(
% 1.46/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
% 1.46/0.56  fof(f152,plain,(
% 1.46/0.56    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl6_8),
% 1.46/0.56    inference(avatar_component_clause,[],[f150])).
% 1.46/0.56  fof(f150,plain,(
% 1.46/0.56    spl6_8 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.46/0.56  fof(f1089,plain,(
% 1.46/0.56    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl6_76),
% 1.46/0.56    inference(avatar_component_clause,[],[f1087])).
% 1.46/0.56  fof(f1087,plain,(
% 1.46/0.56    spl6_76 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 1.46/0.56  fof(f463,plain,(
% 1.46/0.56    ( ! [X4] : (r1_xboole_0(k1_xboole_0,X4)) )),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f462])).
% 1.46/0.56  fof(f462,plain,(
% 1.46/0.56    ( ! [X4] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X4)) )),
% 1.46/0.56    inference(superposition,[],[f98,f457])).
% 1.46/0.56  fof(f457,plain,(
% 1.46/0.56    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7)) )),
% 1.46/0.56    inference(resolution,[],[f371,f166])).
% 1.46/0.56  fof(f166,plain,(
% 1.46/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.46/0.56    inference(resolution,[],[f102,f75])).
% 1.46/0.56  fof(f75,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.46/0.56  fof(f102,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f64])).
% 1.46/0.56  fof(f64,plain,(
% 1.46/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.46/0.56    inference(nnf_transformation,[],[f10])).
% 1.46/0.56  fof(f10,axiom,(
% 1.46/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.46/0.56  fof(f371,plain,(
% 1.46/0.56    ( ! [X10,X9] : (~r1_tarski(X9,k2_xboole_0(X10,k1_xboole_0)) | k1_xboole_0 = k4_xboole_0(X9,X10)) )),
% 1.46/0.56    inference(resolution,[],[f191,f166])).
% 1.46/0.56  fof(f191,plain,(
% 1.46/0.56    ( ! [X6,X7,X5] : (~r1_tarski(X7,k4_xboole_0(X5,X6)) | ~r1_tarski(X5,k2_xboole_0(X6,X7)) | k4_xboole_0(X5,X6) = X7) )),
% 1.46/0.56    inference(resolution,[],[f105,f96])).
% 1.46/0.56  fof(f96,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f60])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.56    inference(flattening,[],[f59])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.56  fof(f105,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.46/0.56  fof(f98,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f61])).
% 1.46/0.56  fof(f61,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.46/0.56    inference(nnf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.46/0.56  fof(f137,plain,(
% 1.46/0.56    l1_orders_2(sK0) | ~spl6_5),
% 1.46/0.56    inference(avatar_component_clause,[],[f135])).
% 1.46/0.56  fof(f135,plain,(
% 1.46/0.56    spl6_5 <=> l1_orders_2(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.46/0.56  fof(f132,plain,(
% 1.46/0.56    v5_orders_2(sK0) | ~spl6_4),
% 1.46/0.56    inference(avatar_component_clause,[],[f130])).
% 1.46/0.56  fof(f130,plain,(
% 1.46/0.56    spl6_4 <=> v5_orders_2(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.46/0.56  fof(f127,plain,(
% 1.46/0.56    v4_orders_2(sK0) | ~spl6_3),
% 1.46/0.56    inference(avatar_component_clause,[],[f125])).
% 1.46/0.56  fof(f125,plain,(
% 1.46/0.56    spl6_3 <=> v4_orders_2(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.46/0.56  fof(f122,plain,(
% 1.46/0.56    v3_orders_2(sK0) | ~spl6_2),
% 1.46/0.56    inference(avatar_component_clause,[],[f120])).
% 1.46/0.56  fof(f120,plain,(
% 1.46/0.56    spl6_2 <=> v3_orders_2(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.46/0.56  fof(f117,plain,(
% 1.46/0.56    ~v2_struct_0(sK0) | spl6_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f115])).
% 1.46/0.56  fof(f115,plain,(
% 1.46/0.56    spl6_1 <=> v2_struct_0(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.46/0.56  fof(f1090,plain,(
% 1.46/0.56    spl6_76 | ~spl6_6 | ~spl6_27 | ~spl6_35 | ~spl6_74),
% 1.46/0.56    inference(avatar_split_clause,[],[f1074,f1058,f413,f374,f140,f1087])).
% 1.46/0.56  fof(f140,plain,(
% 1.46/0.56    spl6_6 <=> m2_orders_2(sK2,sK0,sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.46/0.56  fof(f374,plain,(
% 1.46/0.56    spl6_27 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.46/0.56  fof(f413,plain,(
% 1.46/0.56    spl6_35 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.46/0.56  fof(f1058,plain,(
% 1.46/0.56    spl6_74 <=> m1_orders_2(sK2,sK0,sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 1.46/0.56  fof(f1074,plain,(
% 1.46/0.56    m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl6_6 | ~spl6_27 | ~spl6_35 | ~spl6_74)),
% 1.46/0.56    inference(backward_demodulation,[],[f142,f1073])).
% 1.46/0.56  fof(f1073,plain,(
% 1.46/0.56    k1_xboole_0 = sK2 | (~spl6_27 | ~spl6_35 | ~spl6_74)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1072,f1060])).
% 1.46/0.56  fof(f1060,plain,(
% 1.46/0.56    m1_orders_2(sK2,sK0,sK2) | ~spl6_74),
% 1.46/0.56    inference(avatar_component_clause,[],[f1058])).
% 1.46/0.56  fof(f1072,plain,(
% 1.46/0.56    k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2) | (~spl6_27 | ~spl6_35 | ~spl6_74)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1068,f415])).
% 1.46/0.56  fof(f415,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_35),
% 1.46/0.56    inference(avatar_component_clause,[],[f413])).
% 1.46/0.56  fof(f1068,plain,(
% 1.46/0.56    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(sK2,sK0,sK2) | (~spl6_27 | ~spl6_74)),
% 1.46/0.56    inference(resolution,[],[f1060,f375])).
% 1.46/0.56  fof(f375,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_orders_2(X1,sK0,X0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,X1)) ) | ~spl6_27),
% 1.46/0.56    inference(avatar_component_clause,[],[f374])).
% 1.46/0.56  fof(f142,plain,(
% 1.46/0.56    m2_orders_2(sK2,sK0,sK1) | ~spl6_6),
% 1.46/0.56    inference(avatar_component_clause,[],[f140])).
% 1.46/0.56  fof(f1061,plain,(
% 1.46/0.56    spl6_74 | ~spl6_10 | ~spl6_22),
% 1.46/0.56    inference(avatar_split_clause,[],[f1055,f329,f159,f1058])).
% 1.46/0.56  fof(f159,plain,(
% 1.46/0.56    spl6_10 <=> m1_orders_2(sK2,sK0,sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.46/0.56  fof(f329,plain,(
% 1.46/0.56    spl6_22 <=> sK2 = sK3),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.46/0.56  fof(f1055,plain,(
% 1.46/0.56    m1_orders_2(sK2,sK0,sK2) | (~spl6_10 | ~spl6_22)),
% 1.46/0.56    inference(forward_demodulation,[],[f161,f331])).
% 1.46/0.56  fof(f331,plain,(
% 1.46/0.56    sK2 = sK3 | ~spl6_22),
% 1.46/0.56    inference(avatar_component_clause,[],[f329])).
% 1.46/0.56  fof(f161,plain,(
% 1.46/0.56    m1_orders_2(sK2,sK0,sK3) | ~spl6_10),
% 1.46/0.56    inference(avatar_component_clause,[],[f159])).
% 1.46/0.56  fof(f1049,plain,(
% 1.46/0.56    ~spl6_9 | ~spl6_22),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1048])).
% 1.46/0.56  fof(f1048,plain,(
% 1.46/0.56    $false | (~spl6_9 | ~spl6_22)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1025,f85])).
% 1.46/0.56  fof(f85,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0] : ~r2_xboole_0(X0,X0)),
% 1.46/0.56    inference(rectify,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 1.46/0.56  fof(f1025,plain,(
% 1.46/0.56    r2_xboole_0(sK2,sK2) | (~spl6_9 | ~spl6_22)),
% 1.46/0.56    inference(backward_demodulation,[],[f157,f331])).
% 1.46/0.56  fof(f157,plain,(
% 1.46/0.56    r2_xboole_0(sK2,sK3) | ~spl6_9),
% 1.46/0.56    inference(avatar_component_clause,[],[f155])).
% 1.46/0.56  fof(f155,plain,(
% 1.46/0.56    spl6_9 <=> r2_xboole_0(sK2,sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.46/0.56  fof(f1018,plain,(
% 1.46/0.56    ~spl6_17 | spl6_25 | ~spl6_35 | ~spl6_73),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1017])).
% 1.46/0.56  fof(f1017,plain,(
% 1.46/0.56    $false | (~spl6_17 | spl6_25 | ~spl6_35 | ~spl6_73)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1016,f354])).
% 1.46/0.56  fof(f354,plain,(
% 1.46/0.56    ~r1_tarski(sK3,sK2) | spl6_25),
% 1.46/0.56    inference(avatar_component_clause,[],[f352])).
% 1.46/0.56  fof(f352,plain,(
% 1.46/0.56    spl6_25 <=> r1_tarski(sK3,sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.46/0.56  fof(f1016,plain,(
% 1.46/0.56    r1_tarski(sK3,sK2) | (~spl6_17 | ~spl6_35 | ~spl6_73)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1013,f415])).
% 1.46/0.56  fof(f1013,plain,(
% 1.46/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK3,sK2) | (~spl6_17 | ~spl6_73)),
% 1.46/0.56    inference(resolution,[],[f1002,f291])).
% 1.46/0.56  fof(f291,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1)) ) | ~spl6_17),
% 1.46/0.56    inference(avatar_component_clause,[],[f290])).
% 1.46/0.56  fof(f290,plain,(
% 1.46/0.56    spl6_17 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.46/0.56  fof(f1002,plain,(
% 1.46/0.56    m1_orders_2(sK3,sK0,sK2) | ~spl6_73),
% 1.46/0.56    inference(avatar_component_clause,[],[f1000])).
% 1.46/0.56  fof(f1000,plain,(
% 1.46/0.56    spl6_73 <=> m1_orders_2(sK3,sK0,sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 1.46/0.56  fof(f1003,plain,(
% 1.46/0.56    spl6_73 | spl6_22 | ~spl6_7 | spl6_10 | ~spl6_70),
% 1.46/0.56    inference(avatar_split_clause,[],[f998,f982,f159,f145,f329,f1000])).
% 1.46/0.56  fof(f145,plain,(
% 1.46/0.56    spl6_7 <=> m2_orders_2(sK3,sK0,sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.46/0.56  fof(f982,plain,(
% 1.46/0.56    spl6_70 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 1.46/0.56  fof(f998,plain,(
% 1.46/0.56    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | (~spl6_7 | spl6_10 | ~spl6_70)),
% 1.46/0.56    inference(subsumption_resolution,[],[f996,f160])).
% 1.46/0.56  fof(f160,plain,(
% 1.46/0.56    ~m1_orders_2(sK2,sK0,sK3) | spl6_10),
% 1.46/0.56    inference(avatar_component_clause,[],[f159])).
% 1.46/0.56  fof(f996,plain,(
% 1.46/0.56    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3) | (~spl6_7 | ~spl6_70)),
% 1.46/0.56    inference(resolution,[],[f983,f147])).
% 1.46/0.56  fof(f147,plain,(
% 1.46/0.56    m2_orders_2(sK3,sK0,sK1) | ~spl6_7),
% 1.46/0.56    inference(avatar_component_clause,[],[f145])).
% 1.46/0.56  fof(f983,plain,(
% 1.46/0.56    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) ) | ~spl6_70),
% 1.46/0.56    inference(avatar_component_clause,[],[f982])).
% 1.46/0.56  fof(f984,plain,(
% 1.46/0.56    spl6_70 | ~spl6_6 | ~spl6_42),
% 1.46/0.56    inference(avatar_split_clause,[],[f620,f611,f140,f982])).
% 1.46/0.56  fof(f611,plain,(
% 1.46/0.56    spl6_42 <=> ! [X1,X0] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.46/0.56  fof(f620,plain,(
% 1.46/0.56    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) ) | (~spl6_6 | ~spl6_42)),
% 1.46/0.56    inference(resolution,[],[f612,f142])).
% 1.46/0.56  fof(f612,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | X0 = X1 | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl6_42),
% 1.46/0.56    inference(avatar_component_clause,[],[f611])).
% 1.46/0.56  fof(f619,plain,(
% 1.46/0.56    spl6_42 | ~spl6_8 | ~spl6_31),
% 1.46/0.56    inference(avatar_split_clause,[],[f584,f393,f150,f611])).
% 1.46/0.56  fof(f393,plain,(
% 1.46/0.56    spl6_31 <=> ! [X1,X0,X2] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.46/0.56  fof(f584,plain,(
% 1.46/0.56    ( ! [X0,X1] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | (~spl6_8 | ~spl6_31)),
% 1.46/0.56    inference(resolution,[],[f394,f152])).
% 1.46/0.56  fof(f394,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl6_31),
% 1.46/0.56    inference(avatar_component_clause,[],[f393])).
% 1.46/0.56  fof(f416,plain,(
% 1.46/0.56    spl6_35 | ~spl6_6 | ~spl6_33),
% 1.46/0.56    inference(avatar_split_clause,[],[f410,f403,f140,f413])).
% 1.46/0.56  fof(f403,plain,(
% 1.46/0.56    spl6_33 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.46/0.56  fof(f410,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_6 | ~spl6_33)),
% 1.46/0.56    inference(resolution,[],[f404,f142])).
% 1.46/0.56  fof(f404,plain,(
% 1.46/0.56    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_33),
% 1.46/0.56    inference(avatar_component_clause,[],[f403])).
% 1.46/0.56  fof(f405,plain,(
% 1.46/0.56    spl6_33 | ~spl6_8 | ~spl6_21),
% 1.46/0.56    inference(avatar_split_clause,[],[f350,f321,f150,f403])).
% 1.46/0.56  fof(f321,plain,(
% 1.46/0.56    spl6_21 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.46/0.56  fof(f350,plain,(
% 1.46/0.56    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_8 | ~spl6_21)),
% 1.46/0.56    inference(resolution,[],[f322,f152])).
% 1.46/0.56  fof(f322,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_21),
% 1.46/0.56    inference(avatar_component_clause,[],[f321])).
% 1.46/0.56  fof(f395,plain,(
% 1.46/0.56    spl6_31 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 1.46/0.56    inference(avatar_split_clause,[],[f264,f135,f130,f125,f120,f115,f393])).
% 1.46/0.56  fof(f264,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.56    inference(subsumption_resolution,[],[f263,f117])).
% 1.46/0.56  fof(f263,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.56    inference(subsumption_resolution,[],[f262,f122])).
% 1.46/0.56  fof(f262,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.56    inference(subsumption_resolution,[],[f261,f127])).
% 1.46/0.56  fof(f261,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f260,f132])).
% 1.46/0.57  fof(f260,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_5),
% 1.46/0.57    inference(resolution,[],[f79,f137])).
% 1.46/0.57  fof(f79,plain,(
% 1.46/0.57    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X2,X0,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f55])).
% 1.46/0.57  fof(f55,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(nnf_transformation,[],[f30])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f29])).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f21])).
% 1.46/0.57  fof(f21,axiom,(
% 1.46/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).
% 1.46/0.57  fof(f376,plain,(
% 1.46/0.57    spl6_27 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 1.46/0.57    inference(avatar_split_clause,[],[f253,f135,f130,f125,f120,f115,f374])).
% 1.46/0.57  fof(f253,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f252,f117])).
% 1.46/0.57  fof(f252,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f251,f122])).
% 1.46/0.57  fof(f251,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f250,f127])).
% 1.46/0.57  fof(f250,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f249,f132])).
% 1.46/0.57  fof(f249,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_5),
% 1.46/0.57    inference(resolution,[],[f243,f137])).
% 1.46/0.57  fof(f243,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f81,f93])).
% 1.46/0.57  fof(f93,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f40])).
% 1.46/0.57  fof(f40,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f39])).
% 1.46/0.57  fof(f39,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f16])).
% 1.46/0.57  fof(f16,axiom,(
% 1.46/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 1.46/0.57  fof(f81,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f34])).
% 1.46/0.57  fof(f34,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f33])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f19])).
% 1.46/0.57  fof(f19,axiom,(
% 1.46/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 1.46/0.57  fof(f355,plain,(
% 1.46/0.57    ~spl6_25 | spl6_22 | ~spl6_9),
% 1.46/0.57    inference(avatar_split_clause,[],[f333,f155,f329,f352])).
% 1.46/0.57  fof(f333,plain,(
% 1.46/0.57    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl6_9),
% 1.46/0.57    inference(resolution,[],[f157,f178])).
% 1.46/0.57  fof(f178,plain,(
% 1.46/0.57    ( ! [X4,X3] : (~r2_xboole_0(X4,X3) | X3 = X4 | ~r1_tarski(X3,X4)) )),
% 1.46/0.57    inference(resolution,[],[f96,f99])).
% 1.46/0.57  fof(f99,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f63])).
% 1.46/0.57  fof(f63,plain,(
% 1.46/0.57    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.46/0.57    inference(flattening,[],[f62])).
% 1.46/0.57  fof(f62,plain,(
% 1.46/0.57    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.46/0.57    inference(nnf_transformation,[],[f1])).
% 1.46/0.57  fof(f1,axiom,(
% 1.46/0.57    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.46/0.57  fof(f332,plain,(
% 1.46/0.57    spl6_22 | spl6_9 | ~spl6_19),
% 1.46/0.57    inference(avatar_split_clause,[],[f319,f300,f155,f329])).
% 1.46/0.57  fof(f300,plain,(
% 1.46/0.57    spl6_19 <=> r1_tarski(sK2,sK3)),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.46/0.57  fof(f319,plain,(
% 1.46/0.57    sK2 = sK3 | (spl6_9 | ~spl6_19)),
% 1.46/0.57    inference(subsumption_resolution,[],[f317,f156])).
% 1.46/0.57  fof(f156,plain,(
% 1.46/0.57    ~r2_xboole_0(sK2,sK3) | spl6_9),
% 1.46/0.57    inference(avatar_component_clause,[],[f155])).
% 1.46/0.57  fof(f317,plain,(
% 1.46/0.57    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl6_19),
% 1.46/0.57    inference(resolution,[],[f302,f101])).
% 1.46/0.57  fof(f101,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f63])).
% 1.46/0.57  fof(f302,plain,(
% 1.46/0.57    r1_tarski(sK2,sK3) | ~spl6_19),
% 1.46/0.57    inference(avatar_component_clause,[],[f300])).
% 1.46/0.57  fof(f323,plain,(
% 1.46/0.57    spl6_21 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 1.46/0.57    inference(avatar_split_clause,[],[f231,f135,f130,f125,f120,f115,f321])).
% 1.46/0.57  fof(f231,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f230,f117])).
% 1.46/0.57  fof(f230,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f229,f122])).
% 1.46/0.57  fof(f229,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f228,f127])).
% 1.46/0.57  fof(f228,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f227,f132])).
% 1.46/0.57  fof(f227,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_5),
% 1.46/0.57    inference(resolution,[],[f92,f137])).
% 1.46/0.57  fof(f92,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f38])).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f37])).
% 1.46/0.57  fof(f37,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f17])).
% 1.46/0.57  fof(f17,axiom,(
% 1.46/0.57    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 1.46/0.57  fof(f311,plain,(
% 1.46/0.57    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | spl6_20),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f309])).
% 1.46/0.57  fof(f309,plain,(
% 1.46/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | spl6_20)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f137,f147,f152,f306,f92])).
% 1.46/0.57  fof(f306,plain,(
% 1.46/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_20),
% 1.46/0.57    inference(avatar_component_clause,[],[f304])).
% 1.46/0.57  fof(f304,plain,(
% 1.46/0.57    spl6_20 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.46/0.57  fof(f307,plain,(
% 1.46/0.57    spl6_19 | ~spl6_20 | ~spl6_10 | ~spl6_17),
% 1.46/0.57    inference(avatar_split_clause,[],[f298,f290,f159,f304,f300])).
% 1.46/0.57  fof(f298,plain,(
% 1.46/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3) | (~spl6_10 | ~spl6_17)),
% 1.46/0.57    inference(resolution,[],[f291,f161])).
% 1.46/0.57  fof(f292,plain,(
% 1.46/0.57    spl6_17 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 1.46/0.57    inference(avatar_split_clause,[],[f214,f135,f130,f125,f120,f115,f290])).
% 1.46/0.57  fof(f214,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f213,f117])).
% 1.46/0.57  fof(f213,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f212,f122])).
% 1.46/0.57  fof(f212,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f211,f127])).
% 1.46/0.57  fof(f211,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 1.46/0.57    inference(subsumption_resolution,[],[f210,f132])).
% 1.46/0.57  fof(f210,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_5),
% 1.46/0.57    inference(resolution,[],[f80,f137])).
% 1.46/0.57  fof(f80,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X2,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f32])).
% 1.46/0.57  fof(f32,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f31])).
% 1.46/0.57  fof(f31,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f18])).
% 1.46/0.57  fof(f18,axiom,(
% 1.46/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 1.46/0.57  fof(f164,plain,(
% 1.46/0.57    ~spl6_9 | ~spl6_10),
% 1.46/0.57    inference(avatar_split_clause,[],[f163,f159,f155])).
% 1.46/0.57  fof(f163,plain,(
% 1.46/0.57    ~r2_xboole_0(sK2,sK3) | ~spl6_10),
% 1.46/0.57    inference(subsumption_resolution,[],[f74,f161])).
% 1.46/0.57  fof(f74,plain,(
% 1.46/0.57    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f54,plain,(
% 1.46/0.57    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f53,f52,f51,f50])).
% 1.46/0.57  fof(f50,plain,(
% 1.46/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f51,plain,(
% 1.46/0.57    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f52,plain,(
% 1.46/0.57    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f53,plain,(
% 1.46/0.57    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f49,plain,(
% 1.46/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f48])).
% 1.46/0.57  fof(f48,plain,(
% 1.46/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.46/0.57    inference(nnf_transformation,[],[f26])).
% 1.46/0.57  fof(f26,plain,(
% 1.46/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f25])).
% 1.46/0.57  fof(f25,plain,(
% 1.46/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f23])).
% 1.46/0.57  fof(f23,negated_conjecture,(
% 1.46/0.57    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.46/0.57    inference(negated_conjecture,[],[f22])).
% 1.46/0.57  fof(f22,conjecture,(
% 1.46/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).
% 1.46/0.57  fof(f162,plain,(
% 1.46/0.57    spl6_9 | spl6_10),
% 1.46/0.57    inference(avatar_split_clause,[],[f73,f159,f155])).
% 1.46/0.57  fof(f73,plain,(
% 1.46/0.57    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f153,plain,(
% 1.46/0.57    spl6_8),
% 1.46/0.57    inference(avatar_split_clause,[],[f70,f150])).
% 1.46/0.57  fof(f70,plain,(
% 1.46/0.57    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f148,plain,(
% 1.46/0.57    spl6_7),
% 1.46/0.57    inference(avatar_split_clause,[],[f72,f145])).
% 1.46/0.57  fof(f72,plain,(
% 1.46/0.57    m2_orders_2(sK3,sK0,sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f143,plain,(
% 1.46/0.57    spl6_6),
% 1.46/0.57    inference(avatar_split_clause,[],[f71,f140])).
% 1.46/0.57  fof(f71,plain,(
% 1.46/0.57    m2_orders_2(sK2,sK0,sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f138,plain,(
% 1.46/0.57    spl6_5),
% 1.46/0.57    inference(avatar_split_clause,[],[f69,f135])).
% 1.46/0.57  fof(f69,plain,(
% 1.46/0.57    l1_orders_2(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f133,plain,(
% 1.46/0.57    spl6_4),
% 1.46/0.57    inference(avatar_split_clause,[],[f68,f130])).
% 1.46/0.57  fof(f68,plain,(
% 1.46/0.57    v5_orders_2(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f128,plain,(
% 1.46/0.57    spl6_3),
% 1.46/0.57    inference(avatar_split_clause,[],[f67,f125])).
% 1.46/0.57  fof(f67,plain,(
% 1.46/0.57    v4_orders_2(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f123,plain,(
% 1.46/0.57    spl6_2),
% 1.46/0.57    inference(avatar_split_clause,[],[f66,f120])).
% 1.46/0.57  fof(f66,plain,(
% 1.46/0.57    v3_orders_2(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  fof(f118,plain,(
% 1.46/0.57    ~spl6_1),
% 1.46/0.57    inference(avatar_split_clause,[],[f65,f115])).
% 1.46/0.57  fof(f65,plain,(
% 1.46/0.57    ~v2_struct_0(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f54])).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (6238)------------------------------
% 1.46/0.57  % (6238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (6238)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (6238)Memory used [KB]: 6780
% 1.46/0.57  % (6238)Time elapsed: 0.133 s
% 1.46/0.57  % (6238)------------------------------
% 1.46/0.57  % (6238)------------------------------
% 1.46/0.57  % (6233)Success in time 0.205 s
%------------------------------------------------------------------------------
