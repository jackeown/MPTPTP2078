%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 215 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  368 (1042 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f103,f104,f111,f131,f138,f145,f221,f228,f250,f259,f309,f314,f354,f408,f409])).

fof(f409,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f408,plain,(
    ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl5_28 ),
    inference(resolution,[],[f353,f105])).

fof(f105,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f41,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f353,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl5_28
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f354,plain,
    ( spl5_28
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f322,f135,f96,f351])).

fof(f96,plain,
    ( spl5_8
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f135,plain,
    ( spl5_15
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f322,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(backward_demodulation,[],[f97,f137])).

fof(f137,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f97,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f314,plain,
    ( spl5_15
    | ~ spl5_17
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f310,f306,f218,f135])).

fof(f218,plain,
    ( spl5_17
  <=> r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f306,plain,
    ( spl5_25
  <=> r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f310,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ spl5_25 ),
    inference(resolution,[],[f308,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f308,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f306])).

fof(f309,plain,
    ( ~ spl5_18
    | ~ spl5_9
    | ~ spl5_10
    | spl5_25
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f303,f257,f247,f306,f108,f100,f225])).

fof(f225,plain,
    ( spl5_18
  <=> m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f100,plain,
    ( spl5_9
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f108,plain,
    ( spl5_10
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f247,plain,
    ( spl5_20
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f257,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f303,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(resolution,[],[f258,f249])).

fof(f249,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f247])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( ~ spl5_6
    | spl5_21
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f251,f81,f61,f257,f86])).

fof(f86,plain,
    ( spl5_6
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f61,plain,
    ( spl5_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f81,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f48,f83])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f250,plain,
    ( spl5_20
    | spl5_4
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f244,f225,f71,f66,f61,f76,f247])).

fof(f76,plain,
    ( spl5_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f66,plain,
    ( spl5_2
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f71,plain,
    ( spl5_3
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f244,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1))
    | ~ spl5_18 ),
    inference(resolution,[],[f227,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,k3_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f227,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f225])).

fof(f228,plain,
    ( spl5_18
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f223,f218,f225])).

fof(f223,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_17 ),
    inference(resolution,[],[f220,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f220,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f218])).

fof(f221,plain,
    ( spl5_15
    | spl5_17
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f214,f81,f218,f135])).

fof(f214,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ spl5_5 ),
    inference(factoring,[],[f155])).

fof(f155,plain,
    ( ! [X5] :
        ( r2_hidden(sK4(X5,sK1),X5)
        | r2_hidden(sK4(X5,sK1),u1_struct_0(sK0))
        | sK1 = X5 )
    | ~ spl5_5 ),
    inference(resolution,[],[f56,f146])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f55,f83])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f145,plain,
    ( sK1 != u1_struct_0(sK0)
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f138,plain,
    ( spl5_8
    | spl5_15
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f133,f81,f135,f96])).

fof(f133,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f53,f83])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f131,plain,
    ( spl5_13
    | spl5_14
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f113,f108,f128,f124])).

fof(f124,plain,
    ( spl5_13
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f128,plain,
    ( spl5_14
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f113,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(resolution,[],[f52,f110])).

fof(f110,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f111,plain,
    ( spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f106,f61,f108])).

fof(f106,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f43,f63])).

fof(f63,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f104,plain,
    ( spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f32,f100,f96])).

fof(f32,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
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
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f103,plain,
    ( ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f33,f100,f96])).

fof(f33,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f34,f91])).

fof(f91,plain,
    ( spl5_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f34,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f86])).

% (18795)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f35,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f37,f76])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f66])).

fof(f39,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f40,f61])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:45:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (18779)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.46  % (18786)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.47  % (18786)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f410,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f103,f104,f111,f131,f138,f145,f221,f228,f250,f259,f309,f314,f354,f408,f409])).
% 0.22/0.48  fof(f409,plain,(
% 0.22/0.48    sK1 != u1_struct_0(sK0) | v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f408,plain,(
% 0.22/0.48    ~spl5_28),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f407])).
% 0.22/0.48  fof(f407,plain,(
% 0.22/0.48    $false | ~spl5_28),
% 0.22/0.48    inference(resolution,[],[f353,f105])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f41,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.22/0.48  fof(f353,plain,(
% 0.22/0.48    v1_subset_1(sK1,sK1) | ~spl5_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f351])).
% 0.22/0.48  fof(f351,plain,(
% 0.22/0.48    spl5_28 <=> v1_subset_1(sK1,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.48  fof(f354,plain,(
% 0.22/0.48    spl5_28 | ~spl5_8 | ~spl5_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f322,f135,f96,f351])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl5_8 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    spl5_15 <=> sK1 = u1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.48  fof(f322,plain,(
% 0.22/0.48    v1_subset_1(sK1,sK1) | (~spl5_8 | ~spl5_15)),
% 0.22/0.48    inference(backward_demodulation,[],[f97,f137])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    sK1 = u1_struct_0(sK0) | ~spl5_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f135])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f96])).
% 0.22/0.48  fof(f314,plain,(
% 0.22/0.48    spl5_15 | ~spl5_17 | ~spl5_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f310,f306,f218,f135])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    spl5_17 <=> r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.48  fof(f306,plain,(
% 0.22/0.48    spl5_25 <=> r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.48  fof(f310,plain,(
% 0.22/0.48    ~r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~spl5_25),
% 0.22/0.48    inference(resolution,[],[f308,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.48  fof(f308,plain,(
% 0.22/0.48    r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1) | ~spl5_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f306])).
% 0.22/0.48  fof(f309,plain,(
% 0.22/0.48    ~spl5_18 | ~spl5_9 | ~spl5_10 | spl5_25 | ~spl5_20 | ~spl5_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f303,f257,f247,f306,f108,f100,f225])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    spl5_18 <=> m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    spl5_9 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl5_10 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.48  fof(f247,plain,(
% 0.22/0.48    spl5_20 <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.48  fof(f257,plain,(
% 0.22/0.48    spl5_21 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.48  fof(f303,plain,(
% 0.22/0.48    r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl5_20 | ~spl5_21)),
% 0.22/0.48    inference(resolution,[],[f258,f249])).
% 0.22/0.48  fof(f249,plain,(
% 0.22/0.48    r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1)) | ~spl5_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f247])).
% 0.22/0.48  fof(f258,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f257])).
% 0.22/0.48  fof(f259,plain,(
% 0.22/0.48    ~spl5_6 | spl5_21 | ~spl5_1 | ~spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f251,f81,f61,f257,f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl5_6 <=> v13_waybel_0(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl5_1 <=> l1_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.48  fof(f251,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl5_5),
% 0.22/0.48    inference(resolution,[],[f48,f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f81])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.22/0.48  fof(f250,plain,(
% 0.22/0.48    spl5_20 | spl5_4 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f244,f225,f71,f66,f61,f76,f247])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl5_4 <=> v2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl5_2 <=> v1_yellow_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl5_3 <=> v5_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.48  fof(f244,plain,(
% 0.22/0.48    ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1)) | ~spl5_18),
% 0.22/0.48    inference(resolution,[],[f227,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.22/0.48  fof(f227,plain,(
% 0.22/0.48    m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f225])).
% 0.22/0.48  fof(f228,plain,(
% 0.22/0.48    spl5_18 | ~spl5_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f223,f218,f225])).
% 0.22/0.48  fof(f223,plain,(
% 0.22/0.48    m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_17),
% 0.22/0.48    inference(resolution,[],[f220,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f218])).
% 0.22/0.48  fof(f221,plain,(
% 0.22/0.48    spl5_15 | spl5_17 | ~spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f214,f81,f218,f135])).
% 0.22/0.48  fof(f214,plain,(
% 0.22/0.48    r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~spl5_5),
% 0.22/0.48    inference(factoring,[],[f155])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    ( ! [X5] : (r2_hidden(sK4(X5,sK1),X5) | r2_hidden(sK4(X5,sK1),u1_struct_0(sK0)) | sK1 = X5) ) | ~spl5_5),
% 0.22/0.48    inference(resolution,[],[f56,f146])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0))) ) | ~spl5_5),
% 0.22/0.48    inference(resolution,[],[f55,f83])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    sK1 != u1_struct_0(sK0) | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    spl5_8 | spl5_15 | ~spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f133,f81,f135,f96])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.22/0.48    inference(resolution,[],[f53,f83])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl5_13 | spl5_14 | ~spl5_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f113,f108,f128,f124])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl5_13 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl5_14 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl5_10),
% 0.22/0.48    inference(resolution,[],[f52,f110])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl5_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f108])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    spl5_10 | ~spl5_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f106,f61,f108])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl5_1),
% 0.22/0.48    inference(resolution,[],[f43,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    l1_orders_2(sK0) | ~spl5_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl5_8 | ~spl5_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f100,f96])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ~spl5_8 | spl5_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f100,f96])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ~spl5_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl5_7 <=> v1_xboole_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ~v1_xboole_0(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    spl5_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f86])).
% 0.22/0.48  % (18795)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v13_waybel_0(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f81])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ~spl5_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f76])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl5_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f71])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    v5_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl5_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f39,f66])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    v1_yellow_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl5_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f61])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    l1_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (18786)------------------------------
% 0.22/0.48  % (18786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (18786)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (18786)Memory used [KB]: 11001
% 0.22/0.48  % (18786)Time elapsed: 0.080 s
% 0.22/0.48  % (18786)------------------------------
% 0.22/0.48  % (18786)------------------------------
% 0.22/0.49  % (18769)Success in time 0.123 s
%------------------------------------------------------------------------------
