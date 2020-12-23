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
% DateTime   : Thu Dec  3 13:22:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 201 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :    7
%              Number of atoms          :  384 ( 894 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f84,f89,f94,f104,f109,f121,f130,f131,f137,f157,f197,f202,f213,f221,f236,f242,f273,f275,f276,f278])).

fof(f278,plain,
    ( ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f156,f150,f59])).

fof(f59,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f150,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_15
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f156,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f276,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f275,plain,
    ( spl5_14
    | ~ spl5_31
    | ~ spl5_22
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f274,f270,f195,f270,f134])).

fof(f134,plain,
    ( spl5_14
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f195,plain,
    ( spl5_22
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f270,plain,
    ( spl5_31
  <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f274,plain,
    ( ~ r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ spl5_22
    | ~ spl5_31 ),
    inference(resolution,[],[f272,f198])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,u1_struct_0(sK0)),sK1)
        | ~ r2_hidden(sK4(X0,u1_struct_0(sK0)),X0)
        | u1_struct_0(sK0) = X0 )
    | ~ spl5_22 ),
    inference(resolution,[],[f196,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f196,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f272,plain,
    ( r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f270])).

fof(f273,plain,
    ( spl5_14
    | spl5_31
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f267,f211,f270,f134])).

% (9180)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f211,plain,
    ( spl5_25
  <=> ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f267,plain,
    ( r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ spl5_25 ),
    inference(factoring,[],[f231])).

fof(f231,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(X1,u1_struct_0(sK0)),sK1)
        | r2_hidden(sK4(X1,u1_struct_0(sK0)),X1)
        | u1_struct_0(sK0) = X1 )
    | ~ spl5_25 ),
    inference(resolution,[],[f225,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f225,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl5_25 ),
    inference(resolution,[],[f212,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f212,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f211])).

fof(f242,plain,
    ( sK1 != u1_struct_0(sK0)
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f236,plain,
    ( spl5_26
    | spl5_11
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f223,f207,f118,f233])).

fof(f233,plain,
    ( spl5_26
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f118,plain,
    ( spl5_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f207,plain,
    ( spl5_24
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f223,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl5_24 ),
    inference(resolution,[],[f208,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f208,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f207])).

fof(f221,plain,
    ( ~ spl5_7
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl5_7
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f93,f209,f43])).

fof(f43,plain,(
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

fof(f209,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f207])).

fof(f93,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f213,plain,
    ( spl5_2
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_13
    | ~ spl5_24
    | spl5_25
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f205,f200,f211,f207,f127,f81,f86,f91,f66])).

fof(f66,plain,
    ( spl5_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f86,plain,
    ( spl5_6
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f81,plain,
    ( spl5_5
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f127,plain,
    ( spl5_13
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f200,plain,
    ( spl5_23
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f205,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
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
    | ~ spl5_23 ),
    inference(resolution,[],[f201,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( ~ spl5_9
    | spl5_23
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f112,f106,f91,f200,f101])).

fof(f101,plain,
    ( spl5_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f106,plain,
    ( spl5_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl5_10 ),
    inference(resolution,[],[f108,f48])).

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

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f197,plain,
    ( spl5_11
    | spl5_22
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f132,f106,f195,f118])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl5_10 ),
    inference(resolution,[],[f113,f53])).

fof(f113,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_10 ),
    inference(resolution,[],[f108,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

% (9157)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f157,plain,
    ( spl5_16
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f141,f134,f106,f154])).

fof(f141,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f108,f136])).

fof(f136,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f137,plain,
    ( spl5_12
    | spl5_14
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f114,f106,f134,f123])).

fof(f123,plain,
    ( spl5_12
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f114,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(resolution,[],[f108,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f131,plain,
    ( ~ spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f30,f127,f123])).

fof(f30,plain,
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

fof(f130,plain,
    ( spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f29,f127,f123])).

fof(f29,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f121,plain,
    ( spl5_1
    | ~ spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f115,f106,f118,f61])).

fof(f61,plain,
    ( spl5_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f115,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f108,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f109,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f34,f106])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f33,f101])).

fof(f33,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (9167)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (9176)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (9172)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (9165)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (9160)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (9176)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f64,f69,f84,f89,f94,f104,f109,f121,f130,f131,f137,f157,f197,f202,f213,f221,f236,f242,f273,f275,f276,f278])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    ~spl5_15 | ~spl5_16),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f277])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    $false | (~spl5_15 | ~spl5_16)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f156,f150,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    v1_subset_1(sK1,sK1) | ~spl5_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f149])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl5_15 <=> v1_subset_1(sK1,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl5_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f154])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    spl5_16 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    sK1 != u1_struct_0(sK0) | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    spl5_14 | ~spl5_31 | ~spl5_22 | ~spl5_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f274,f270,f195,f270,f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    spl5_14 <=> sK1 = u1_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    spl5_22 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.53  fof(f270,plain,(
% 0.22/0.53    spl5_31 <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    ~r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) | sK1 = u1_struct_0(sK0) | (~spl5_22 | ~spl5_31)),
% 0.22/0.53    inference(resolution,[],[f272,f198])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK4(X0,u1_struct_0(sK0)),sK1) | ~r2_hidden(sK4(X0,u1_struct_0(sK0)),X0) | u1_struct_0(sK0) = X0) ) | ~spl5_22),
% 0.22/0.53    inference(resolution,[],[f196,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | ~spl5_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f195])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) | ~spl5_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f270])).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    spl5_14 | spl5_31 | ~spl5_25),
% 0.22/0.53    inference(avatar_split_clause,[],[f267,f211,f270,f134])).
% 0.22/0.53  % (9180)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    spl5_25 <=> ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.53  fof(f267,plain,(
% 0.22/0.53    r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) | sK1 = u1_struct_0(sK0) | ~spl5_25),
% 0.22/0.53    inference(factoring,[],[f231])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(sK4(X1,u1_struct_0(sK0)),sK1) | r2_hidden(sK4(X1,u1_struct_0(sK0)),X1) | u1_struct_0(sK0) = X1) ) | ~spl5_25),
% 0.22/0.53    inference(resolution,[],[f225,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1)) ) | ~spl5_25),
% 0.22/0.53    inference(resolution,[],[f212,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1)) ) | ~spl5_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f211])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    sK1 != u1_struct_0(sK0) | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    spl5_26 | spl5_11 | ~spl5_24),
% 0.22/0.53    inference(avatar_split_clause,[],[f223,f207,f118,f233])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    spl5_26 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl5_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    spl5_24 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl5_24),
% 0.22/0.53    inference(resolution,[],[f208,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl5_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f207])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    ~spl5_7 | spl5_24),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f215])).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    $false | (~spl5_7 | spl5_24)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f93,f209,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | spl5_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f207])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    l1_orders_2(sK0) | ~spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl5_7 <=> l1_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    spl5_2 | ~spl5_7 | ~spl5_6 | ~spl5_5 | ~spl5_13 | ~spl5_24 | spl5_25 | ~spl5_23),
% 0.22/0.53    inference(avatar_split_clause,[],[f205,f200,f211,f207,f127,f81,f86,f91,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl5_2 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl5_6 <=> v1_yellow_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl5_5 <=> v5_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    spl5_13 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    spl5_23 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_23),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f204])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | ~spl5_23),
% 0.22/0.53    inference(resolution,[],[f201,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f200])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ~spl5_9 | spl5_23 | ~spl5_7 | ~spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f112,f106,f91,f200,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl5_9 <=> v13_waybel_0(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl5_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl5_10),
% 0.22/0.53    inference(resolution,[],[f108,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    spl5_11 | spl5_22 | ~spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f132,f106,f195,f118])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(X0,u1_struct_0(sK0))) ) | ~spl5_10),
% 0.22/0.53    inference(resolution,[],[f113,f53])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X2] : (m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1)) ) | ~spl5_10),
% 0.22/0.53    inference(resolution,[],[f108,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  % (9157)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    spl5_16 | ~spl5_10 | ~spl5_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f141,f134,f106,f154])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl5_10 | ~spl5_14)),
% 0.22/0.53    inference(backward_demodulation,[],[f108,f136])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    sK1 = u1_struct_0(sK0) | ~spl5_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f134])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl5_12 | spl5_14 | ~spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f114,f106,f134,f123])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl5_12 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_10),
% 0.22/0.53    inference(resolution,[],[f108,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ~spl5_12 | spl5_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f127,f123])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    spl5_12 | ~spl5_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f127,f123])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    spl5_1 | ~spl5_11 | ~spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f115,f106,f118,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl5_1 <=> v1_xboole_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1) | ~spl5_10),
% 0.22/0.53    inference(resolution,[],[f108,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f106])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl5_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f101])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    v13_waybel_0(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f91])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    l1_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f86])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v1_yellow_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f81])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    v5_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ~spl5_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f66])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ~spl5_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f61])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ~v1_xboole_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (9176)------------------------------
% 0.22/0.53  % (9176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9176)Termination reason: Refutation
% 0.22/0.53  % (9171)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  
% 0.22/0.53  % (9176)Memory used [KB]: 10874
% 0.22/0.53  % (9176)Time elapsed: 0.069 s
% 0.22/0.53  % (9176)------------------------------
% 0.22/0.53  % (9176)------------------------------
% 0.22/0.53  % (9171)Refutation not found, incomplete strategy% (9171)------------------------------
% 0.22/0.53  % (9171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9148)Success in time 0.17 s
%------------------------------------------------------------------------------
