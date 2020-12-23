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
% DateTime   : Thu Dec  3 13:23:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 187 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :    7
%              Number of atoms          :  337 ( 626 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f77,f83,f95,f102,f108,f116,f141,f154,f159,f174,f187,f207])).

fof(f207,plain,
    ( spl5_13
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f206,f184,f113])).

fof(f113,plain,
    ( spl5_13
  <=> r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f184,plain,
    ( spl5_25
  <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f206,plain,
    ( r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_25 ),
    inference(resolution,[],[f186,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f186,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f184])).

fof(f187,plain,
    ( spl5_13
    | spl5_25
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f176,f171,f152,f184,f113])).

fof(f152,plain,
    ( spl5_20
  <=> ! [X3] :
        ( r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X3)
        | r2_hidden(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X3),sK1,sK2),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f171,plain,
    ( spl5_23
  <=> sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f176,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))
    | r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(superposition,[],[f153,f173])).

fof(f173,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f171])).

fof(f153,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X3),sK1,sK2),u1_struct_0(sK1))
        | r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X3) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f174,plain,
    ( spl5_23
    | ~ spl5_6
    | spl5_13
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f169,f157,f113,f68,f171])).

fof(f68,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f157,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
        | sK3(a_3_0_waybel_9(sK0,sK1,X0),X1) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f169,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ spl5_6
    | spl5_13
    | ~ spl5_21 ),
    inference(resolution,[],[f162,f115])).

fof(f115,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f162,plain,
    ( ! [X0] :
        ( r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X0)
        | sK3(a_3_0_waybel_9(sK0,sK1,sK2),X0) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X0),sK1,sK2) )
    | ~ spl5_6
    | ~ spl5_21 ),
    inference(resolution,[],[f158,f70])).

fof(f70,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
        | sK3(a_3_0_waybel_9(sK0,sK1,X0),X1) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( spl5_2
    | spl5_21
    | ~ spl5_1
    | spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f155,f53,f58,f43,f157,f48])).

fof(f48,plain,
    ( spl5_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f43,plain,
    ( spl5_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f58,plain,
    ( spl5_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f53,plain,
    ( spl5_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | sK3(a_3_0_waybel_9(sK0,sK1,X0),X1) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0)
        | v2_struct_0(sK0)
        | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f109,f55])).

fof(f55,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK3(a_3_0_waybel_9(X0,X1,X2),X3) = sK4(sK3(a_3_0_waybel_9(X0,X1,X2),X3),X1,X2)
      | v2_struct_0(X0)
      | r1_tarski(a_3_0_waybel_9(X0,X1,X2),X3) ) ),
    inference(resolution,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | sK4(X0,X2,X3) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

% (23368)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(f154,plain,
    ( spl5_10
    | spl5_20
    | ~ spl5_6
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f150,f139,f68,f152,f90])).

fof(f90,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f139,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
        | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f150,plain,
    ( ! [X3] :
        ( r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X3)
        | v1_xboole_0(u1_struct_0(sK1))
        | r2_hidden(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X3),sK1,sK2),u1_struct_0(sK1)) )
    | ~ spl5_6
    | ~ spl5_18 ),
    inference(resolution,[],[f142,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f142,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X0),sK1,sK2),u1_struct_0(sK1))
        | r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X0) )
    | ~ spl5_6
    | ~ spl5_18 ),
    inference(resolution,[],[f140,f70])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
        | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0),u1_struct_0(sK1)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl5_2
    | spl5_18
    | ~ spl5_1
    | spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f137,f53,f58,f43,f139,f48])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f130,f55])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(sK4(sK3(a_3_0_waybel_9(X0,X1,X2),X3),X1,X2),u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_tarski(a_3_0_waybel_9(X0,X1,X2),X3) ) ),
    inference(resolution,[],[f37,f35])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,
    ( ~ spl5_13
    | spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f110,f105,f63,f113])).

fof(f63,plain,
    ( spl5_5
  <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f105,plain,
    ( spl5_12
  <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f110,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl5_5
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f65,f107])).

fof(f107,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f65,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f108,plain,
    ( spl5_12
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f103,f100,f68,f105])).

fof(f100,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f103,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(resolution,[],[f101,f70])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl5_11
    | spl5_2
    | spl5_4
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f98,f53,f43,f58,f48,f100])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f33,f55])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).

fof(f95,plain,
    ( spl5_4
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f94,f90,f80,f58])).

fof(f80,plain,
    ( spl5_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f94,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f92,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).

fof(f92,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f83,plain,
    ( spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f78,f74,f80])).

fof(f74,plain,
    ( spl5_7
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f78,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f76,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f76,plain,
    ( l1_orders_2(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f77,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f72,f53,f43,f74])).

fof(f72,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f32,f55])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f71,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f23,f68])).

fof(f23,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f66,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f24,f63])).

fof(f24,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f43])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (23365)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (23365)Refutation not found, incomplete strategy% (23365)------------------------------
% 0.22/0.55  % (23365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23365)Memory used [KB]: 1791
% 0.22/0.55  % (23365)Time elapsed: 0.112 s
% 0.22/0.55  % (23365)------------------------------
% 0.22/0.55  % (23365)------------------------------
% 0.22/0.55  % (23381)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (23381)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f77,f83,f95,f102,f108,f116,f141,f154,f159,f174,f187,f207])).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    spl5_13 | ~spl5_25),
% 0.22/0.55    inference(avatar_split_clause,[],[f206,f184,f113])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    spl5_13 <=> r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.55  fof(f184,plain,(
% 0.22/0.55    spl5_25 <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | ~spl5_25),
% 0.22/0.55    inference(resolution,[],[f186,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) | ~spl5_25),
% 0.22/0.55    inference(avatar_component_clause,[],[f184])).
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    spl5_13 | spl5_25 | ~spl5_20 | ~spl5_23),
% 0.22/0.55    inference(avatar_split_clause,[],[f176,f171,f152,f184,f113])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    spl5_20 <=> ! [X3] : (r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X3) | r2_hidden(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X3),sK1,sK2),u1_struct_0(sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    spl5_23 <=> sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) | r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | (~spl5_20 | ~spl5_23)),
% 0.22/0.55    inference(superposition,[],[f153,f173])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~spl5_23),
% 0.22/0.55    inference(avatar_component_clause,[],[f171])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ( ! [X3] : (r2_hidden(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X3),sK1,sK2),u1_struct_0(sK1)) | r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X3)) ) | ~spl5_20),
% 0.22/0.55    inference(avatar_component_clause,[],[f152])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    spl5_23 | ~spl5_6 | spl5_13 | ~spl5_21),
% 0.22/0.55    inference(avatar_split_clause,[],[f169,f157,f113,f68,f171])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    spl5_6 <=> m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    spl5_21 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | sK3(a_3_0_waybel_9(sK0,sK1,X0),X1) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | (~spl5_6 | spl5_13 | ~spl5_21)),
% 0.22/0.55    inference(resolution,[],[f162,f115])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | spl5_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f113])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X0) | sK3(a_3_0_waybel_9(sK0,sK1,sK2),X0) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X0),sK1,sK2)) ) | (~spl5_6 | ~spl5_21)),
% 0.22/0.55    inference(resolution,[],[f158,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl5_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | sK3(a_3_0_waybel_9(sK0,sK1,X0),X1) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0)) ) | ~spl5_21),
% 0.22/0.55    inference(avatar_component_clause,[],[f157])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    spl5_2 | spl5_21 | ~spl5_1 | spl5_4 | ~spl5_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f155,f53,f58,f43,f157,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    spl5_2 <=> v2_struct_0(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    spl5_1 <=> l1_struct_0(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    spl5_4 <=> v2_struct_0(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    spl5_3 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v2_struct_0(sK1) | ~l1_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | sK3(a_3_0_waybel_9(sK0,sK1,X0),X1) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0) | v2_struct_0(sK0) | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)) ) | ~spl5_3),
% 0.22/0.55    inference(resolution,[],[f109,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    l1_waybel_0(sK1,sK0) | ~spl5_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f53])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | sK3(a_3_0_waybel_9(X0,X1,X2),X3) = sK4(sK3(a_3_0_waybel_9(X0,X1,X2),X3),X1,X2) | v2_struct_0(X0) | r1_tarski(a_3_0_waybel_9(X0,X1,X2),X3)) )),
% 0.22/0.55    inference(resolution,[],[f38,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | sK4(X0,X2,X3) = X0 | v2_struct_0(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | (~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  % (23368)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X2)) & l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    spl5_10 | spl5_20 | ~spl5_6 | ~spl5_18),
% 0.22/0.55    inference(avatar_split_clause,[],[f150,f139,f68,f152,f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    spl5_10 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    spl5_18 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0),u1_struct_0(sK1)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    ( ! [X3] : (r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X3) | v1_xboole_0(u1_struct_0(sK1)) | r2_hidden(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X3),sK1,sK2),u1_struct_0(sK1))) ) | (~spl5_6 | ~spl5_18)),
% 0.22/0.56    inference(resolution,[],[f142,f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),X0),sK1,sK2),u1_struct_0(sK1)) | r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),X0)) ) | (~spl5_6 | ~spl5_18)),
% 0.22/0.56    inference(resolution,[],[f140,f70])).
% 0.22/0.56  fof(f140,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0),u1_struct_0(sK1))) ) | ~spl5_18),
% 0.22/0.56    inference(avatar_component_clause,[],[f139])).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    spl5_2 | spl5_18 | ~spl5_1 | spl5_4 | ~spl5_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f137,f53,f58,f43,f139,f48])).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v2_struct_0(sK1) | ~l1_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,X0),X1),sK1,X0),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)) ) | ~spl5_3),
% 0.22/0.56    inference(resolution,[],[f130,f55])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(sK4(sK3(a_3_0_waybel_9(X0,X1,X2),X3),X1,X2),u1_struct_0(X1)) | v2_struct_0(X0) | r1_tarski(a_3_0_waybel_9(X0,X1,X2),X3)) )),
% 0.22/0.56    inference(resolution,[],[f37,f35])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2)) | v2_struct_0(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    ~spl5_13 | spl5_5 | ~spl5_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f110,f105,f63,f113])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    spl5_5 <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    spl5_12 <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | (spl5_5 | ~spl5_12)),
% 0.22/0.56    inference(backward_demodulation,[],[f65,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) | ~spl5_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f105])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | spl5_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f63])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    spl5_12 | ~spl5_6 | ~spl5_11),
% 0.22/0.56    inference(avatar_split_clause,[],[f103,f100,f68,f105])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    spl5_11 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) | (~spl5_6 | ~spl5_11)),
% 0.22/0.56    inference(resolution,[],[f101,f70])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)) ) | ~spl5_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f100])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    spl5_11 | spl5_2 | spl5_4 | ~spl5_1 | ~spl5_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f98,f53,f43,f58,f48,f100])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)) ) | ~spl5_3),
% 0.22/0.56    inference(resolution,[],[f33,f55])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    spl5_4 | ~spl5_8 | ~spl5_10),
% 0.22/0.56    inference(avatar_split_clause,[],[f94,f90,f80,f58])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    spl5_8 <=> l1_struct_0(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_10),
% 0.22/0.56    inference(resolution,[],[f92,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0] : ((v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f90])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    spl5_8 | ~spl5_7),
% 0.22/0.56    inference(avatar_split_clause,[],[f78,f74,f80])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    spl5_7 <=> l1_orders_2(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    l1_struct_0(sK1) | ~spl5_7),
% 0.22/0.56    inference(resolution,[],[f76,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    l1_orders_2(sK1) | ~spl5_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f74])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    spl5_7 | ~spl5_1 | ~spl5_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f72,f53,f43,f74])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ~l1_struct_0(sK0) | l1_orders_2(sK1) | ~spl5_3),
% 0.22/0.56    inference(resolution,[],[f32,f55])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    spl5_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f23,f68])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.22/0.56    inference(negated_conjecture,[],[f8])).
% 0.22/0.56  fof(f8,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ~spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f24,f63])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ~spl5_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f25,f58])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ~v2_struct_0(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    spl5_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f26,f53])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    l1_waybel_0(sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ~spl5_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f27,f48])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ~v2_struct_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    spl5_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f28,f43])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    l1_struct_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (23381)------------------------------
% 0.22/0.56  % (23381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23381)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (23381)Memory used [KB]: 10874
% 0.22/0.56  % (23381)Time elapsed: 0.120 s
% 0.22/0.56  % (23381)------------------------------
% 0.22/0.56  % (23381)------------------------------
% 0.22/0.56  % (23364)Success in time 0.194 s
%------------------------------------------------------------------------------
