%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:56 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 711 expanded)
%              Number of leaves         :   27 ( 185 expanded)
%              Depth                    :   14
%              Number of atoms          :  523 (4680 expanded)
%              Number of equality atoms :   27 (  81 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2511,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f122,f183,f259,f263,f267,f411,f498,f614,f741,f1092,f1109,f1562,f1946,f2208,f2506,f2510])).

fof(f2510,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f2507])).

fof(f2507,plain,
    ( $false
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f38,f254])).

fof(f254,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f2506,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f2502])).

fof(f2502,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f326,f2222,f71])).

fof(f71,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f2222,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f102,f218])).

fof(f218,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl7_3
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f102,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_1
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f326,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f97,f236])).

fof(f236,plain,
    ( sK1 = k4_waybel_0(sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl7_5
  <=> sK1 = k4_waybel_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f97,plain,(
    m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f84,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f84,plain,(
    r1_tarski(k4_waybel_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f43,f36,f37,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f2208,plain,
    ( ~ spl7_22
    | spl7_25 ),
    inference(avatar_contradiction_clause,[],[f2205])).

fof(f2205,plain,
    ( $false
    | ~ spl7_22
    | spl7_25 ),
    inference(unit_resulting_resolution,[],[f1136,f2151,f1087])).

fof(f1087,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0))
        | r1_tarski(X0,sK1) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1086,plain,
    ( spl7_22
  <=> ! [X0] :
        ( ~ m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0))
        | r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f2151,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl7_25 ),
    inference(unit_resulting_resolution,[],[f2024,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f2024,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl7_25 ),
    inference(unit_resulting_resolution,[],[f1136,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f1136,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f1135,plain,
    ( spl7_25
  <=> r1_tarski(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1946,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | ~ spl7_25
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f1942])).

fof(f1942,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_25
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f326,f1619,f71])).

fof(f1619,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_25
    | ~ spl7_32 ),
    inference(backward_demodulation,[],[f102,f1592])).

fof(f1592,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_25
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f326,f1183,f1561,f1570,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f1570,plain,
    ( r2_hidden(sK5(sK1,sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f85,f1561,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1561,plain,
    ( r2_hidden(sK5(sK1,sK1,u1_struct_0(sK0)),sK1)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f1559])).

fof(f1559,plain,
    ( spl7_32
  <=> r2_hidden(sK5(sK1,sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f1183,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1))
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f1137,f66])).

fof(f1137,plain,
    ( r1_tarski(u1_struct_0(sK0),sK1)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f1562,plain,
    ( spl7_32
    | spl7_3
    | ~ spl7_5
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f1283,f1135,f234,f216,f1559])).

fof(f1283,plain,
    ( sK1 = u1_struct_0(sK0)
    | r2_hidden(sK5(sK1,sK1,u1_struct_0(sK0)),sK1)
    | ~ spl7_5
    | ~ spl7_25 ),
    inference(resolution,[],[f1183,f514])).

fof(f514,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | sK1 = X0
        | r2_hidden(sK5(sK1,sK1,X0),sK1) )
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f506,f236])).

fof(f506,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | r2_hidden(sK5(sK1,k4_waybel_0(sK0,sK1),X0),sK1) )
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f288,f236])).

fof(f288,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | k4_waybel_0(sK0,sK1) = X0
      | r2_hidden(sK5(sK1,k4_waybel_0(sK0,sK1),X0),sK1) ) ),
    inference(resolution,[],[f120,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f34,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f34,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f120,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(sK1,k4_waybel_0(sK0,sK1),X4),sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | k4_waybel_0(sK0,sK1) = X4 ) ),
    inference(resolution,[],[f97,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1109,plain,(
    spl7_23 ),
    inference(avatar_contradiction_clause,[],[f1095])).

fof(f1095,plain,
    ( $false
    | spl7_23 ),
    inference(unit_resulting_resolution,[],[f43,f1091,f48])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f1091,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f1089])).

fof(f1089,plain,
    ( spl7_23
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1092,plain,
    ( spl7_22
    | ~ spl7_23
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f981,f739,f245,f104,f1089,f1086])).

fof(f104,plain,
    ( spl7_2
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f245,plain,
    ( spl7_6
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f739,plain,
    ( spl7_16
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1)
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f981,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0))
        | r1_tarski(X0,sK1) )
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(duplicate_literal_removal,[],[f978])).

fof(f978,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0))
        | r1_tarski(X0,sK1)
        | ~ m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(resolution,[],[f770,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f245])).

fof(f770,plain,
    ( ! [X12,X13] :
        ( ~ r1_orders_2(sK0,X13,sK6(X12,sK1))
        | ~ r2_hidden(X13,sK1)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(X12,sK1),u1_struct_0(sK0))
        | r1_tarski(X12,sK1) )
    | ~ spl7_16 ),
    inference(resolution,[],[f740,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f740,plain,
    ( ! [X4,X3] :
        ( r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X3) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f739])).

fof(f741,plain,
    ( spl7_16
    | ~ spl7_7
    | ~ spl7_13
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f548,f234,f603,f248,f739])).

fof(f248,plain,
    ( spl7_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f603,plain,
    ( spl7_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f548,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X3)
        | ~ r2_hidden(X4,sK1)
        | r2_hidden(X3,sK1) )
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f547])).

fof(f547,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X3)
        | ~ r2_hidden(X4,sK1)
        | r2_hidden(X3,sK1) )
    | ~ spl7_5 ),
    inference(superposition,[],[f72,f236])).

fof(f72,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_waybel_0)).

fof(f614,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f85,f605,f66])).

fof(f605,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f603])).

fof(f498,plain,
    ( ~ spl7_2
    | spl7_5
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl7_2
    | spl7_5
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f84,f461,f450,f68])).

fof(f450,plain,
    ( r2_hidden(sK6(k4_waybel_0(sK0,sK1),u1_struct_0(sK0)),k4_waybel_0(sK0,sK1))
    | ~ spl7_2
    | spl7_5
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f448,f69])).

fof(f448,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_2
    | spl7_5
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f446,f66])).

fof(f446,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | spl7_5
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f43,f105,f37,f78,f419,f367,f395,f72])).

fof(f395,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK2(sK0,sK1,sK1))
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f41,f42,f43,f38,f367,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,k3_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f42,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f367,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f43,f37,f37,f235,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k4_waybel_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f235,plain,
    ( sK1 != k4_waybel_0(sK0,sK1)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f234])).

fof(f419,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k4_waybel_0(sK0,sK1))
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f97,f318,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f318,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl7_10
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f78,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f43,f48])).

fof(f105,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f461,plain,
    ( ~ r2_hidden(sK6(k4_waybel_0(sK0,sK1),u1_struct_0(sK0)),sK1)
    | ~ spl7_2
    | spl7_5
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f37,f451,f45])).

fof(f451,plain,
    ( ~ r2_hidden(sK6(k4_waybel_0(sK0,sK1),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_2
    | spl7_5
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f448,f70])).

fof(f411,plain,
    ( ~ spl7_2
    | spl7_5
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl7_2
    | spl7_5
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f42,f41,f43,f38,f367,f378,f47])).

fof(f378,plain,
    ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK2(sK0,sK1,sK1))
    | ~ spl7_2
    | spl7_5
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f105,f78,f235,f37,f37,f319,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X2,sK2(sK0,X0,X1))
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_waybel_0(sK0,X0) = X1 ) ),
    inference(resolution,[],[f43,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_waybel_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f319,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f317])).

fof(f267,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl7_9 ),
    inference(unit_resulting_resolution,[],[f41,f258])).

fof(f258,plain,
    ( ~ v5_orders_2(sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl7_9
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f263,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f43,f250])).

fof(f250,plain,
    ( ~ l1_orders_2(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f248])).

fof(f259,plain,
    ( spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f77,f256,f252,f248,f245])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    inference(resolution,[],[f42,f47])).

fof(f183,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f34,f106,f126,f53])).

fof(f126,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl7_1 ),
    inference(backward_demodulation,[],[f78,f123])).

fof(f123,plain,
    ( sK1 = u1_struct_0(sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f37,f101,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f106,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f122,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f33,f104,f100])).

fof(f33,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f32,f104,f100])).

fof(f32,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (14238)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (14232)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (14246)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (14244)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (14256)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (14233)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (14255)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (14257)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (14237)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (14258)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (14239)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (14235)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (14242)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (14236)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (14245)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (14248)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (14259)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (14247)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (14249)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (14261)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (14262)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (14260)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (14254)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (14251)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (14243)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (14250)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (14263)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (14241)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (14243)Refutation not found, incomplete strategy% (14243)------------------------------
% 0.21/0.55  % (14243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14243)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14243)Memory used [KB]: 10746
% 0.21/0.55  % (14243)Time elapsed: 0.142 s
% 0.21/0.55  % (14243)------------------------------
% 0.21/0.55  % (14243)------------------------------
% 0.21/0.55  % (14240)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (14260)Refutation not found, incomplete strategy% (14260)------------------------------
% 0.21/0.56  % (14260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14260)Memory used [KB]: 10874
% 0.21/0.56  % (14260)Time elapsed: 0.153 s
% 0.21/0.56  % (14260)------------------------------
% 0.21/0.56  % (14260)------------------------------
% 2.11/0.64  % (14370)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.23/0.65  % (14237)Refutation found. Thanks to Tanya!
% 2.23/0.65  % SZS status Theorem for theBenchmark
% 2.23/0.65  % SZS output start Proof for theBenchmark
% 2.23/0.65  fof(f2511,plain,(
% 2.23/0.65    $false),
% 2.23/0.65    inference(avatar_sat_refutation,[],[f107,f122,f183,f259,f263,f267,f411,f498,f614,f741,f1092,f1109,f1562,f1946,f2208,f2506,f2510])).
% 2.23/0.65  fof(f2510,plain,(
% 2.23/0.65    ~spl7_8),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f2507])).
% 2.23/0.65  fof(f2507,plain,(
% 2.23/0.65    $false | ~spl7_8),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f38,f254])).
% 2.23/0.65  fof(f254,plain,(
% 2.23/0.65    v2_struct_0(sK0) | ~spl7_8),
% 2.23/0.65    inference(avatar_component_clause,[],[f252])).
% 2.23/0.65  fof(f252,plain,(
% 2.23/0.65    spl7_8 <=> v2_struct_0(sK0)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.23/0.65  fof(f38,plain,(
% 2.23/0.65    ~v2_struct_0(sK0)),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  fof(f16,plain,(
% 2.23/0.65    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.23/0.65    inference(flattening,[],[f15])).
% 2.23/0.65  fof(f15,plain,(
% 2.23/0.65    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f14])).
% 2.23/0.65  fof(f14,negated_conjecture,(
% 2.23/0.65    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.23/0.65    inference(negated_conjecture,[],[f13])).
% 2.23/0.65  fof(f13,conjecture,(
% 2.23/0.65    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 2.23/0.65  fof(f2506,plain,(
% 2.23/0.65    ~spl7_1 | ~spl7_3 | ~spl7_5),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f2502])).
% 2.23/0.65  fof(f2502,plain,(
% 2.23/0.65    $false | (~spl7_1 | ~spl7_3 | ~spl7_5)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f326,f2222,f71])).
% 2.23/0.65  fof(f71,plain,(
% 2.23/0.65    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 2.23/0.65    inference(equality_resolution,[],[f50])).
% 2.23/0.65  fof(f50,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f24])).
% 2.23/0.65  fof(f24,plain,(
% 2.23/0.65    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f12])).
% 2.23/0.65  fof(f12,axiom,(
% 2.23/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 2.23/0.65  fof(f2222,plain,(
% 2.23/0.65    v1_subset_1(sK1,sK1) | (~spl7_1 | ~spl7_3)),
% 2.23/0.65    inference(backward_demodulation,[],[f102,f218])).
% 2.23/0.65  fof(f218,plain,(
% 2.23/0.65    sK1 = u1_struct_0(sK0) | ~spl7_3),
% 2.23/0.65    inference(avatar_component_clause,[],[f216])).
% 2.23/0.65  fof(f216,plain,(
% 2.23/0.65    spl7_3 <=> sK1 = u1_struct_0(sK0)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.23/0.65  fof(f102,plain,(
% 2.23/0.65    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_1),
% 2.23/0.65    inference(avatar_component_clause,[],[f100])).
% 2.23/0.65  fof(f100,plain,(
% 2.23/0.65    spl7_1 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.23/0.65  fof(f326,plain,(
% 2.23/0.65    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl7_5),
% 2.23/0.65    inference(backward_demodulation,[],[f97,f236])).
% 2.23/0.65  fof(f236,plain,(
% 2.23/0.65    sK1 = k4_waybel_0(sK0,sK1) | ~spl7_5),
% 2.23/0.65    inference(avatar_component_clause,[],[f234])).
% 2.23/0.65  fof(f234,plain,(
% 2.23/0.65    spl7_5 <=> sK1 = k4_waybel_0(sK0,sK1)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.23/0.65  fof(f97,plain,(
% 2.23/0.65    m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f84,f66])).
% 2.23/0.65  fof(f66,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.23/0.65    inference(cnf_transformation,[],[f6])).
% 2.23/0.65  fof(f6,axiom,(
% 2.23/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.23/0.65  fof(f84,plain,(
% 2.23/0.65    r1_tarski(k4_waybel_0(sK0,sK1),sK1)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f43,f36,f37,f52])).
% 2.23/0.65  fof(f52,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k4_waybel_0(X0,X1),X1) | ~v13_waybel_0(X1,X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f25])).
% 2.23/0.65  fof(f25,plain,(
% 2.23/0.65    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> r1_tarski(k4_waybel_0(X0,X1),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.23/0.65    inference(ennf_transformation,[],[f11])).
% 2.23/0.65  fof(f11,axiom,(
% 2.23/0.65    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> r1_tarski(k4_waybel_0(X0,X1),X1))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).
% 2.23/0.65  fof(f37,plain,(
% 2.23/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  fof(f36,plain,(
% 2.23/0.65    v13_waybel_0(sK1,sK0)),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  fof(f43,plain,(
% 2.23/0.65    l1_orders_2(sK0)),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  fof(f2208,plain,(
% 2.23/0.65    ~spl7_22 | spl7_25),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f2205])).
% 2.23/0.65  fof(f2205,plain,(
% 2.23/0.65    $false | (~spl7_22 | spl7_25)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f1136,f2151,f1087])).
% 2.23/0.65  fof(f1087,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0)) | r1_tarski(X0,sK1)) ) | ~spl7_22),
% 2.23/0.65    inference(avatar_component_clause,[],[f1086])).
% 2.23/0.65  fof(f1086,plain,(
% 2.23/0.65    spl7_22 <=> ! [X0] : (~m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0)) | r1_tarski(X0,sK1))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.23/0.65  fof(f2151,plain,(
% 2.23/0.65    m1_subset_1(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl7_25),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f2024,f46])).
% 2.23/0.65  fof(f46,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f20])).
% 2.23/0.65  fof(f20,plain,(
% 2.23/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.23/0.65    inference(ennf_transformation,[],[f4])).
% 2.23/0.65  fof(f4,axiom,(
% 2.23/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 2.23/0.65  fof(f2024,plain,(
% 2.23/0.65    r2_hidden(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl7_25),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f1136,f69])).
% 2.23/0.65  fof(f69,plain,(
% 2.23/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f31])).
% 2.23/0.65  fof(f31,plain,(
% 2.23/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f1])).
% 2.23/0.65  fof(f1,axiom,(
% 2.23/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.23/0.65  fof(f1136,plain,(
% 2.23/0.65    ~r1_tarski(u1_struct_0(sK0),sK1) | spl7_25),
% 2.23/0.65    inference(avatar_component_clause,[],[f1135])).
% 2.23/0.65  fof(f1135,plain,(
% 2.23/0.65    spl7_25 <=> r1_tarski(u1_struct_0(sK0),sK1)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.23/0.65  fof(f1946,plain,(
% 2.23/0.65    ~spl7_1 | ~spl7_5 | ~spl7_25 | ~spl7_32),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f1942])).
% 2.23/0.65  fof(f1942,plain,(
% 2.23/0.65    $false | (~spl7_1 | ~spl7_5 | ~spl7_25 | ~spl7_32)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f326,f1619,f71])).
% 2.23/0.65  fof(f1619,plain,(
% 2.23/0.65    v1_subset_1(sK1,sK1) | (~spl7_1 | ~spl7_5 | ~spl7_25 | ~spl7_32)),
% 2.23/0.65    inference(backward_demodulation,[],[f102,f1592])).
% 2.23/0.65  fof(f1592,plain,(
% 2.23/0.65    sK1 = u1_struct_0(sK0) | (~spl7_5 | ~spl7_25 | ~spl7_32)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f326,f1183,f1561,f1570,f64])).
% 2.23/0.65  fof(f64,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | X1 = X2) )),
% 2.23/0.65    inference(cnf_transformation,[],[f30])).
% 2.23/0.65  fof(f30,plain,(
% 2.23/0.65    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.23/0.65    inference(flattening,[],[f29])).
% 2.23/0.65  fof(f29,plain,(
% 2.23/0.65    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f3])).
% 2.23/0.65  fof(f3,axiom,(
% 2.23/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 2.23/0.65  fof(f1570,plain,(
% 2.23/0.65    r2_hidden(sK5(sK1,sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl7_32),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f85,f1561,f68])).
% 2.23/0.65  fof(f68,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f31])).
% 2.23/0.65  fof(f85,plain,(
% 2.23/0.65    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f37,f67])).
% 2.23/0.65  fof(f67,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f6])).
% 2.23/0.65  fof(f1561,plain,(
% 2.23/0.65    r2_hidden(sK5(sK1,sK1,u1_struct_0(sK0)),sK1) | ~spl7_32),
% 2.23/0.65    inference(avatar_component_clause,[],[f1559])).
% 2.23/0.65  fof(f1559,plain,(
% 2.23/0.65    spl7_32 <=> r2_hidden(sK5(sK1,sK1,u1_struct_0(sK0)),sK1)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 2.23/0.65  fof(f1183,plain,(
% 2.23/0.65    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1)) | ~spl7_25),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f1137,f66])).
% 2.23/0.65  fof(f1137,plain,(
% 2.23/0.65    r1_tarski(u1_struct_0(sK0),sK1) | ~spl7_25),
% 2.23/0.65    inference(avatar_component_clause,[],[f1135])).
% 2.23/0.65  fof(f1562,plain,(
% 2.23/0.65    spl7_32 | spl7_3 | ~spl7_5 | ~spl7_25),
% 2.23/0.65    inference(avatar_split_clause,[],[f1283,f1135,f234,f216,f1559])).
% 2.23/0.65  fof(f1283,plain,(
% 2.23/0.65    sK1 = u1_struct_0(sK0) | r2_hidden(sK5(sK1,sK1,u1_struct_0(sK0)),sK1) | (~spl7_5 | ~spl7_25)),
% 2.23/0.65    inference(resolution,[],[f1183,f514])).
% 2.23/0.65  fof(f514,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | sK1 = X0 | r2_hidden(sK5(sK1,sK1,X0),sK1)) ) | ~spl7_5),
% 2.23/0.65    inference(forward_demodulation,[],[f506,f236])).
% 2.23/0.65  fof(f506,plain,(
% 2.23/0.65    ( ! [X0] : (sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | r2_hidden(sK5(sK1,k4_waybel_0(sK0,sK1),X0),sK1)) ) | ~spl7_5),
% 2.23/0.65    inference(backward_demodulation,[],[f288,f236])).
% 2.23/0.65  fof(f288,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k4_waybel_0(sK0,sK1) = X0 | r2_hidden(sK5(sK1,k4_waybel_0(sK0,sK1),X0),sK1)) )),
% 2.23/0.65    inference(resolution,[],[f120,f76])).
% 2.23/0.65  fof(f76,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(X0,sK1)) )),
% 2.23/0.65    inference(resolution,[],[f34,f53])).
% 2.23/0.65  fof(f53,plain,(
% 2.23/0.65    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f27])).
% 2.23/0.65  fof(f27,plain,(
% 2.23/0.65    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.23/0.65    inference(flattening,[],[f26])).
% 2.23/0.65  fof(f26,plain,(
% 2.23/0.65    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.23/0.65    inference(ennf_transformation,[],[f5])).
% 2.23/0.65  fof(f5,axiom,(
% 2.23/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.23/0.65  fof(f34,plain,(
% 2.23/0.65    ~v1_xboole_0(sK1)),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  fof(f120,plain,(
% 2.23/0.65    ( ! [X4] : (m1_subset_1(sK5(sK1,k4_waybel_0(sK0,sK1),X4),sK1) | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | k4_waybel_0(sK0,sK1) = X4) )),
% 2.23/0.65    inference(resolution,[],[f97,f65])).
% 2.23/0.65  fof(f65,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK5(X0,X1,X2),X0) | X1 = X2) )),
% 2.23/0.65    inference(cnf_transformation,[],[f30])).
% 2.23/0.65  fof(f1109,plain,(
% 2.23/0.65    spl7_23),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f1095])).
% 2.23/0.65  fof(f1095,plain,(
% 2.23/0.65    $false | spl7_23),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f43,f1091,f48])).
% 2.23/0.65  fof(f48,plain,(
% 2.23/0.65    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f23])).
% 2.23/0.65  fof(f23,plain,(
% 2.23/0.65    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.23/0.65    inference(ennf_transformation,[],[f8])).
% 2.23/0.65  fof(f8,axiom,(
% 2.23/0.65    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 2.23/0.65  fof(f1091,plain,(
% 2.23/0.65    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | spl7_23),
% 2.23/0.65    inference(avatar_component_clause,[],[f1089])).
% 2.23/0.65  fof(f1089,plain,(
% 2.23/0.65    spl7_23 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.23/0.65  fof(f1092,plain,(
% 2.23/0.65    spl7_22 | ~spl7_23 | ~spl7_2 | ~spl7_6 | ~spl7_16),
% 2.23/0.65    inference(avatar_split_clause,[],[f981,f739,f245,f104,f1089,f1086])).
% 2.23/0.65  fof(f104,plain,(
% 2.23/0.65    spl7_2 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.23/0.65  fof(f245,plain,(
% 2.23/0.65    spl7_6 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.23/0.65  fof(f739,plain,(
% 2.23/0.65    spl7_16 <=> ! [X3,X4] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,sK1) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,X3))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.23/0.65  fof(f981,plain,(
% 2.23/0.65    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0)) | r1_tarski(X0,sK1)) ) | (~spl7_6 | ~spl7_16)),
% 2.23/0.65    inference(duplicate_literal_removal,[],[f978])).
% 2.23/0.65  fof(f978,plain,(
% 2.23/0.65    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0)) | r1_tarski(X0,sK1) | ~m1_subset_1(sK6(X0,sK1),u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_16)),
% 2.23/0.65    inference(resolution,[],[f770,f246])).
% 2.23/0.65  fof(f246,plain,(
% 2.23/0.65    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_6),
% 2.23/0.65    inference(avatar_component_clause,[],[f245])).
% 2.23/0.65  fof(f770,plain,(
% 2.23/0.65    ( ! [X12,X13] : (~r1_orders_2(sK0,X13,sK6(X12,sK1)) | ~r2_hidden(X13,sK1) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(sK6(X12,sK1),u1_struct_0(sK0)) | r1_tarski(X12,sK1)) ) | ~spl7_16),
% 2.23/0.65    inference(resolution,[],[f740,f70])).
% 2.23/0.65  fof(f70,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f31])).
% 2.23/0.65  fof(f740,plain,(
% 2.23/0.65    ( ! [X4,X3] : (r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,X3)) ) | ~spl7_16),
% 2.23/0.65    inference(avatar_component_clause,[],[f739])).
% 2.23/0.65  fof(f741,plain,(
% 2.23/0.65    spl7_16 | ~spl7_7 | ~spl7_13 | ~spl7_5),
% 2.23/0.65    inference(avatar_split_clause,[],[f548,f234,f603,f248,f739])).
% 2.23/0.65  fof(f248,plain,(
% 2.23/0.65    spl7_7 <=> l1_orders_2(sK0)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.23/0.65  fof(f603,plain,(
% 2.23/0.65    spl7_13 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.23/0.65  fof(f548,plain,(
% 2.23/0.65    ( ! [X4,X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,X3) | ~r2_hidden(X4,sK1) | r2_hidden(X3,sK1)) ) | ~spl7_5),
% 2.23/0.65    inference(duplicate_literal_removal,[],[f547])).
% 2.23/0.65  fof(f547,plain,(
% 2.23/0.65    ( ! [X4,X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,X3) | ~r2_hidden(X4,sK1) | r2_hidden(X3,sK1)) ) | ~spl7_5),
% 2.23/0.65    inference(superposition,[],[f72,f236])).
% 2.23/0.65  fof(f72,plain,(
% 2.23/0.65    ( ! [X4,X0,X3,X1] : (~m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X4,X3) | ~r2_hidden(X4,X1) | r2_hidden(X3,k4_waybel_0(X0,X1))) )),
% 2.23/0.65    inference(equality_resolution,[],[f57])).
% 2.23/0.65  fof(f57,plain,(
% 2.23/0.65    ( ! [X4,X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X4,X3) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k4_waybel_0(X0,X1) != X2) )),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f28,plain,(
% 2.23/0.65    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_0(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.23/0.65    inference(ennf_transformation,[],[f10])).
% 2.23/0.65  fof(f10,axiom,(
% 2.23/0.65    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k4_waybel_0(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0)))))))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_waybel_0)).
% 2.23/0.65  fof(f614,plain,(
% 2.23/0.65    spl7_13),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f609])).
% 2.23/0.65  fof(f609,plain,(
% 2.23/0.65    $false | spl7_13),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f85,f605,f66])).
% 2.23/0.65  fof(f605,plain,(
% 2.23/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_13),
% 2.23/0.65    inference(avatar_component_clause,[],[f603])).
% 2.23/0.65  fof(f498,plain,(
% 2.23/0.65    ~spl7_2 | spl7_5 | spl7_10),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f489])).
% 2.23/0.65  fof(f489,plain,(
% 2.23/0.65    $false | (~spl7_2 | spl7_5 | spl7_10)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f84,f461,f450,f68])).
% 2.23/0.65  fof(f450,plain,(
% 2.23/0.65    r2_hidden(sK6(k4_waybel_0(sK0,sK1),u1_struct_0(sK0)),k4_waybel_0(sK0,sK1)) | (~spl7_2 | spl7_5 | spl7_10)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f448,f69])).
% 2.23/0.65  fof(f448,plain,(
% 2.23/0.65    ~r1_tarski(k4_waybel_0(sK0,sK1),u1_struct_0(sK0)) | (~spl7_2 | spl7_5 | spl7_10)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f446,f66])).
% 2.23/0.65  fof(f446,plain,(
% 2.23/0.65    ~m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_2 | spl7_5 | spl7_10)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f43,f105,f37,f78,f419,f367,f395,f72])).
% 2.23/0.65  fof(f395,plain,(
% 2.23/0.65    r1_orders_2(sK0,k3_yellow_0(sK0),sK2(sK0,sK1,sK1)) | spl7_5),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f41,f42,f43,f38,f367,f47])).
% 2.23/0.65  fof(f47,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,k3_yellow_0(X0),X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f22])).
% 2.23/0.65  fof(f22,plain,(
% 2.23/0.65    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.23/0.65    inference(flattening,[],[f21])).
% 2.23/0.65  fof(f21,plain,(
% 2.23/0.65    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f9])).
% 2.23/0.65  fof(f9,axiom,(
% 2.23/0.65    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 2.23/0.65  fof(f42,plain,(
% 2.23/0.65    v1_yellow_0(sK0)),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  fof(f41,plain,(
% 2.23/0.65    v5_orders_2(sK0)),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  fof(f367,plain,(
% 2.23/0.65    m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | spl7_5),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f43,f37,f37,f235,f62])).
% 2.23/0.65  fof(f62,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k4_waybel_0(X0,X1) = X2) )),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f235,plain,(
% 2.23/0.65    sK1 != k4_waybel_0(sK0,sK1) | spl7_5),
% 2.23/0.65    inference(avatar_component_clause,[],[f234])).
% 2.23/0.65  fof(f419,plain,(
% 2.23/0.65    ~r2_hidden(sK2(sK0,sK1,sK1),k4_waybel_0(sK0,sK1)) | spl7_10),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f97,f318,f45])).
% 2.23/0.65  fof(f45,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f19])).
% 2.23/0.65  fof(f19,plain,(
% 2.23/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f2])).
% 2.23/0.65  fof(f2,axiom,(
% 2.23/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.23/0.65  fof(f318,plain,(
% 2.23/0.65    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl7_10),
% 2.23/0.65    inference(avatar_component_clause,[],[f317])).
% 2.23/0.65  fof(f317,plain,(
% 2.23/0.65    spl7_10 <=> r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.23/0.65  fof(f78,plain,(
% 2.23/0.65    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f43,f48])).
% 2.23/0.65  fof(f105,plain,(
% 2.23/0.65    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl7_2),
% 2.23/0.65    inference(avatar_component_clause,[],[f104])).
% 2.23/0.65  fof(f461,plain,(
% 2.23/0.65    ~r2_hidden(sK6(k4_waybel_0(sK0,sK1),u1_struct_0(sK0)),sK1) | (~spl7_2 | spl7_5 | spl7_10)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f37,f451,f45])).
% 2.23/0.65  fof(f451,plain,(
% 2.23/0.65    ~r2_hidden(sK6(k4_waybel_0(sK0,sK1),u1_struct_0(sK0)),u1_struct_0(sK0)) | (~spl7_2 | spl7_5 | spl7_10)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f448,f70])).
% 2.23/0.65  fof(f411,plain,(
% 2.23/0.65    ~spl7_2 | spl7_5 | ~spl7_10),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f408])).
% 2.23/0.65  fof(f408,plain,(
% 2.23/0.65    $false | (~spl7_2 | spl7_5 | ~spl7_10)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f42,f41,f43,f38,f367,f378,f47])).
% 2.23/0.65  fof(f378,plain,(
% 2.23/0.65    ~r1_orders_2(sK0,k3_yellow_0(sK0),sK2(sK0,sK1,sK1)) | (~spl7_2 | spl7_5 | ~spl7_10)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f105,f78,f235,f37,f37,f319,f79])).
% 2.23/0.65  fof(f79,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~r2_hidden(sK2(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK2(sK0,X0,X1)) | ~r2_hidden(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_waybel_0(sK0,X0) = X1) )),
% 2.23/0.65    inference(resolution,[],[f43,f58])).
% 2.23/0.65  fof(f58,plain,(
% 2.23/0.65    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X4,sK2(X0,X1,X2)) | ~r2_hidden(X4,X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_waybel_0(X0,X1) = X2) )),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f319,plain,(
% 2.23/0.65    r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~spl7_10),
% 2.23/0.65    inference(avatar_component_clause,[],[f317])).
% 2.23/0.65  fof(f267,plain,(
% 2.23/0.65    spl7_9),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f264])).
% 2.23/0.65  fof(f264,plain,(
% 2.23/0.65    $false | spl7_9),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f41,f258])).
% 2.23/0.65  fof(f258,plain,(
% 2.23/0.65    ~v5_orders_2(sK0) | spl7_9),
% 2.23/0.65    inference(avatar_component_clause,[],[f256])).
% 2.23/0.65  fof(f256,plain,(
% 2.23/0.65    spl7_9 <=> v5_orders_2(sK0)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.23/0.65  fof(f263,plain,(
% 2.23/0.65    spl7_7),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f260])).
% 2.23/0.65  fof(f260,plain,(
% 2.23/0.65    $false | spl7_7),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f43,f250])).
% 2.23/0.65  fof(f250,plain,(
% 2.23/0.65    ~l1_orders_2(sK0) | spl7_7),
% 2.23/0.65    inference(avatar_component_clause,[],[f248])).
% 2.23/0.65  fof(f259,plain,(
% 2.23/0.65    spl7_6 | ~spl7_7 | spl7_8 | ~spl7_9),
% 2.23/0.65    inference(avatar_split_clause,[],[f77,f256,f252,f248,f245])).
% 2.23/0.65  fof(f77,plain,(
% 2.23/0.65    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0)) )),
% 2.23/0.65    inference(resolution,[],[f42,f47])).
% 2.23/0.65  fof(f183,plain,(
% 2.23/0.65    spl7_1 | spl7_2),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f177])).
% 2.23/0.65  fof(f177,plain,(
% 2.23/0.65    $false | (spl7_1 | spl7_2)),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f34,f106,f126,f53])).
% 2.23/0.65  fof(f126,plain,(
% 2.23/0.65    m1_subset_1(k3_yellow_0(sK0),sK1) | spl7_1),
% 2.23/0.65    inference(backward_demodulation,[],[f78,f123])).
% 2.23/0.65  fof(f123,plain,(
% 2.23/0.65    sK1 = u1_struct_0(sK0) | spl7_1),
% 2.23/0.65    inference(unit_resulting_resolution,[],[f37,f101,f49])).
% 2.23/0.65  fof(f49,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f24])).
% 2.23/0.65  fof(f101,plain,(
% 2.23/0.65    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl7_1),
% 2.23/0.65    inference(avatar_component_clause,[],[f100])).
% 2.23/0.65  fof(f106,plain,(
% 2.23/0.65    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl7_2),
% 2.23/0.65    inference(avatar_component_clause,[],[f104])).
% 2.23/0.65  fof(f122,plain,(
% 2.23/0.65    ~spl7_1 | spl7_2),
% 2.23/0.65    inference(avatar_split_clause,[],[f33,f104,f100])).
% 2.23/0.65  fof(f33,plain,(
% 2.23/0.65    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  fof(f107,plain,(
% 2.23/0.65    spl7_1 | ~spl7_2),
% 2.23/0.65    inference(avatar_split_clause,[],[f32,f104,f100])).
% 2.23/0.65  fof(f32,plain,(
% 2.23/0.65    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 2.23/0.65    inference(cnf_transformation,[],[f16])).
% 2.23/0.65  % SZS output end Proof for theBenchmark
% 2.23/0.65  % (14237)------------------------------
% 2.23/0.65  % (14237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.65  % (14237)Termination reason: Refutation
% 2.23/0.65  
% 2.23/0.65  % (14237)Memory used [KB]: 7291
% 2.23/0.65  % (14237)Time elapsed: 0.230 s
% 2.23/0.65  % (14237)------------------------------
% 2.23/0.65  % (14237)------------------------------
% 2.23/0.66  % (14227)Success in time 0.299 s
%------------------------------------------------------------------------------
