%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 213 expanded)
%              Number of leaves         :   30 (  90 expanded)
%              Depth                    :    7
%              Number of atoms          :  391 ( 929 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f86,f91,f96,f106,f111,f133,f134,f146,f151,f162,f173,f182,f197,f207,f212,f227,f246,f249,f283,f293,f301])).

fof(f301,plain,
    ( ~ spl6_27
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl6_27
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f282,f292,f61])).

fof(f61,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f292,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl6_29
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f282,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl6_27
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f293,plain,
    ( spl6_29
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f250,f148,f108,f290])).

fof(f108,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f148,plain,
    ( spl6_16
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f250,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f110,f150])).

fof(f150,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f110,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f283,plain,
    ( spl6_27
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f254,f148,f126,f280])).

fof(f126,plain,
    ( spl6_12
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f254,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f128,f150])).

fof(f128,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f249,plain,
    ( spl6_16
    | ~ spl6_26
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f247,f243,f108,f243,f148])).

% (10125)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f243,plain,
    ( spl6_26
  <=> r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f247,plain,
    ( ~ r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(resolution,[],[f245,f138])).

fof(f138,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1)
        | ~ r2_hidden(sK5(X1,u1_struct_0(sK0)),X1)
        | u1_struct_0(sK0) = X1 )
    | ~ spl6_10 ),
    inference(resolution,[],[f116,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f116,plain,
    ( ! [X3] :
        ( r2_hidden(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl6_10 ),
    inference(resolution,[],[f110,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f245,plain,
    ( r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f243])).

fof(f246,plain,
    ( spl6_16
    | spl6_26
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f240,f210,f243,f148])).

fof(f210,plain,
    ( spl6_22
  <=> ! [X4] :
        ( r2_hidden(X4,sK1)
        | ~ r2_hidden(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f240,plain,
    ( r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ spl6_22 ),
    inference(factoring,[],[f216])).

fof(f216,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1)
        | r2_hidden(sK5(X1,u1_struct_0(sK0)),X1)
        | u1_struct_0(sK0) = X1 )
    | ~ spl6_22 ),
    inference(resolution,[],[f211,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f211,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,u1_struct_0(sK0))
        | r2_hidden(X4,sK1) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f227,plain,
    ( sK1 != u1_struct_0(sK0)
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f212,plain,
    ( spl6_14
    | spl6_22
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f192,f171,f210,f140])).

fof(f140,plain,
    ( spl6_14
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f171,plain,
    ( spl6_20
  <=> ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f192,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK1)
        | ~ r2_hidden(X4,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl6_20 ),
    inference(resolution,[],[f172,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f172,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f207,plain,
    ( spl6_1
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl6_1
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f65,f145,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f145,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_15
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f65,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f197,plain,
    ( spl6_14
    | spl6_21
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f185,f167,f194,f140])).

fof(f194,plain,
    ( spl6_21
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f167,plain,
    ( spl6_19
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f185,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(resolution,[],[f168,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f168,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f182,plain,
    ( ~ spl6_7
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl6_7
    | spl6_19 ),
    inference(unit_resulting_resolution,[],[f95,f169,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f169,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f95,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f173,plain,
    ( spl6_2
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_19
    | spl6_20
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f165,f160,f171,f167,f130,f83,f88,f93,f68])).

fof(f68,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f88,plain,
    ( spl6_6
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f83,plain,
    ( spl6_5
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f130,plain,
    ( spl6_13
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f160,plain,
    ( spl6_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f165,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_18 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_18 ),
    inference(resolution,[],[f161,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( ~ spl6_9
    | spl6_18
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f114,f108,f93,f160,f103])).

fof(f103,plain,
    ( spl6_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f110,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f151,plain,
    ( spl6_12
    | spl6_16
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f117,f108,f148,f126])).

fof(f117,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(resolution,[],[f110,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f146,plain,
    ( ~ spl6_14
    | spl6_15
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f137,f108,f144,f140])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f116,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f134,plain,
    ( ~ spl6_12
    | spl6_13 ),
    inference(avatar_split_clause,[],[f28,f130,f126])).

fof(f28,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f133,plain,
    ( spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f27,f130,f126])).

fof(f27,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f111,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f32,f108])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f106,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f31,f103])).

fof(f31,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f38,f93])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (10126)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (10148)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (10132)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (10139)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (10129)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (10131)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (10143)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (10137)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (10148)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f66,f71,f86,f91,f96,f106,f111,f133,f134,f146,f151,f162,f173,f182,f197,f207,f212,f227,f246,f249,f283,f293,f301])).
% 0.20/0.52  fof(f301,plain,(
% 0.20/0.52    ~spl6_27 | ~spl6_29),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f294])).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    $false | (~spl6_27 | ~spl6_29)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f282,f292,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl6_29),
% 0.20/0.52    inference(avatar_component_clause,[],[f290])).
% 0.20/0.52  fof(f290,plain,(
% 0.20/0.52    spl6_29 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    v1_subset_1(sK1,sK1) | ~spl6_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f280])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    spl6_27 <=> v1_subset_1(sK1,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.52  fof(f293,plain,(
% 0.20/0.52    spl6_29 | ~spl6_10 | ~spl6_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f250,f148,f108,f290])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl6_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    spl6_16 <=> sK1 = u1_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.52  fof(f250,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl6_10 | ~spl6_16)),
% 0.20/0.52    inference(backward_demodulation,[],[f110,f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    sK1 = u1_struct_0(sK0) | ~spl6_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f148])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f108])).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    spl6_27 | ~spl6_12 | ~spl6_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f254,f148,f126,f280])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    spl6_12 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.52  fof(f254,plain,(
% 0.20/0.52    v1_subset_1(sK1,sK1) | (~spl6_12 | ~spl6_16)),
% 0.20/0.52    inference(backward_demodulation,[],[f128,f150])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f126])).
% 0.20/0.52  fof(f249,plain,(
% 0.20/0.52    spl6_16 | ~spl6_26 | ~spl6_10 | ~spl6_26),
% 0.20/0.52    inference(avatar_split_clause,[],[f247,f243,f108,f243,f148])).
% 0.20/0.52  % (10125)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  fof(f243,plain,(
% 0.20/0.52    spl6_26 <=> r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.52  fof(f247,plain,(
% 0.20/0.52    ~r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1) | sK1 = u1_struct_0(sK0) | (~spl6_10 | ~spl6_26)),
% 0.20/0.52    inference(resolution,[],[f245,f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1) | ~r2_hidden(sK5(X1,u1_struct_0(sK0)),X1) | u1_struct_0(sK0) = X1) ) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f116,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ( ! [X3] : (r2_hidden(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1)) ) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f110,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f245,plain,(
% 0.20/0.52    r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1) | ~spl6_26),
% 0.20/0.52    inference(avatar_component_clause,[],[f243])).
% 0.20/0.52  fof(f246,plain,(
% 0.20/0.52    spl6_16 | spl6_26 | ~spl6_22),
% 0.20/0.52    inference(avatar_split_clause,[],[f240,f210,f243,f148])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    spl6_22 <=> ! [X4] : (r2_hidden(X4,sK1) | ~r2_hidden(X4,u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1) | sK1 = u1_struct_0(sK0) | ~spl6_22),
% 0.20/0.52    inference(factoring,[],[f216])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1) | r2_hidden(sK5(X1,u1_struct_0(sK0)),X1) | u1_struct_0(sK0) = X1) ) | ~spl6_22),
% 0.20/0.52    inference(resolution,[],[f211,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    ( ! [X4] : (~r2_hidden(X4,u1_struct_0(sK0)) | r2_hidden(X4,sK1)) ) | ~spl6_22),
% 0.20/0.52    inference(avatar_component_clause,[],[f210])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    sK1 != u1_struct_0(sK0) | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    spl6_14 | spl6_22 | ~spl6_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f192,f171,f210,f140])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    spl6_14 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    spl6_20 <=> ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    ( ! [X4] : (r2_hidden(X4,sK1) | ~r2_hidden(X4,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl6_20),
% 0.20/0.52    inference(resolution,[],[f172,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1)) ) | ~spl6_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f171])).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    spl6_1 | ~spl6_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    $false | (spl6_1 | ~spl6_15)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f65,f145,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl6_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f144])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl6_15 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ~v1_xboole_0(sK1) | spl6_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl6_1 <=> v1_xboole_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    spl6_14 | spl6_21 | ~spl6_19),
% 0.20/0.52    inference(avatar_split_clause,[],[f185,f167,f194,f140])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    spl6_21 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    spl6_19 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl6_19),
% 0.20/0.52    inference(resolution,[],[f168,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl6_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f167])).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    ~spl6_7 | spl6_19),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    $false | (~spl6_7 | spl6_19)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f95,f169,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | spl6_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f167])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    l1_orders_2(sK0) | ~spl6_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    spl6_7 <=> l1_orders_2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    spl6_2 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_13 | ~spl6_19 | spl6_20 | ~spl6_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f165,f160,f171,f167,f130,f83,f88,f93,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl6_2 <=> v2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl6_6 <=> v1_yellow_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl6_5 <=> v5_orders_2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    spl6_13 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    spl6_18 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_18),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f164])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | ~spl6_18),
% 0.20/0.52    inference(resolution,[],[f161,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f160])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    ~spl6_9 | spl6_18 | ~spl6_7 | ~spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f114,f108,f93,f160,f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl6_9 <=> v13_waybel_0(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f110,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    spl6_12 | spl6_16 | ~spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f117,f108,f148,f126])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f110,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    ~spl6_14 | spl6_15 | ~spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f137,f108,f144,f140])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(u1_struct_0(sK0))) ) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f116,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    ~spl6_12 | spl6_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f130,f126])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    spl6_12 | ~spl6_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f27,f130,f126])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f32,f108])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    spl6_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f31,f103])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    v13_waybel_0(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    spl6_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f93])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    l1_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    spl6_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f88])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    v1_yellow_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    spl6_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f83])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    v5_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ~spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f33,f68])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ~spl6_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f29,f63])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~v1_xboole_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (10148)------------------------------
% 0.20/0.52  % (10148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10148)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (10148)Memory used [KB]: 10874
% 0.20/0.52  % (10148)Time elapsed: 0.072 s
% 0.20/0.52  % (10148)------------------------------
% 0.20/0.52  % (10148)------------------------------
% 0.20/0.53  % (10147)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.53  % (10128)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  % (10127)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (10151)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.53  % (10124)Success in time 0.175 s
%------------------------------------------------------------------------------
