%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 423 expanded)
%              Number of leaves         :   45 ( 214 expanded)
%              Depth                    :    9
%              Number of atoms          :  873 (2659 expanded)
%              Number of equality atoms :   28 (  64 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f141,f146,f160,f172,f177,f178,f182,f222,f224,f228,f236,f241,f242,f271,f276,f284,f289,f292,f295,f299,f301])).

fof(f301,plain,
    ( spl3_2
    | ~ spl3_28
    | ~ spl3_1
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f300,f269,f81,f238,f85])).

fof(f85,plain,
    ( spl3_2
  <=> r1_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f238,plain,
    ( spl3_28
  <=> m1_subset_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f81,plain,
    ( spl3_1
  <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f269,plain,
    ( spl3_34
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | r1_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f300,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ spl3_1
    | ~ spl3_34 ),
    inference(resolution,[],[f82,f270])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r1_waybel_7(sK0,sK1,X0) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f269])).

fof(f82,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f299,plain,
    ( ~ spl3_2
    | ~ spl3_28
    | spl3_1
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f296,f274,f81,f238,f85])).

fof(f274,plain,
    ( spl3_35
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ r1_waybel_7(sK0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f296,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_35 ),
    inference(resolution,[],[f275,f83])).

fof(f83,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f275,plain,
    ( ! [X1] :
        ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X1) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f274])).

fof(f295,plain,
    ( ~ spl3_13
    | spl3_11
    | ~ spl3_24
    | ~ spl3_16
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f294,f253,f214,f166,f206,f131,f143])).

fof(f143,plain,
    ( spl3_13
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f131,plain,
    ( spl3_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f206,plain,
    ( spl3_24
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f166,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f214,plain,
    ( spl3_26
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f253,plain,
    ( spl3_30
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f294,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl3_16
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f293,f215])).

fof(f215,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f293,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(resolution,[],[f255,f167])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f255,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f253])).

fof(f292,plain,
    ( ~ spl3_13
    | spl3_11
    | ~ spl3_24
    | ~ spl3_18
    | ~ spl3_26
    | spl3_33 ),
    inference(avatar_split_clause,[],[f291,f265,f214,f175,f206,f131,f143])).

fof(f175,plain,
    ( spl3_18
  <=> ! [X3] :
        ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
        | v2_struct_0(X3)
        | ~ l1_struct_0(X3)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f265,plain,
    ( spl3_33
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f291,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl3_18
    | ~ spl3_26
    | spl3_33 ),
    inference(forward_demodulation,[],[f290,f215])).

fof(f290,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_18
    | spl3_33 ),
    inference(resolution,[],[f176,f267])).

fof(f267,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f265])).

fof(f176,plain,
    ( ! [X3] :
        ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
        | v2_struct_0(X3)
        | ~ l1_struct_0(X3)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f289,plain,
    ( spl3_31
    | ~ spl3_13
    | spl3_11
    | ~ spl3_24
    | ~ spl3_19
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f286,f214,f180,f206,f131,f143,f257])).

fof(f257,plain,
    ( spl3_31
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f180,plain,
    ( spl3_19
  <=> ! [X5] :
        ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f286,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_19
    | ~ spl3_26 ),
    inference(superposition,[],[f181,f215])).

fof(f181,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5)
        | v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f180])).

fof(f284,plain,
    ( spl3_32
    | ~ spl3_13
    | spl3_11
    | ~ spl3_24
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f281,f214,f170,f206,f131,f143,f261])).

fof(f261,plain,
    ( spl3_32
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f170,plain,
    ( spl3_17
  <=> ! [X1] :
        ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
        | v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f281,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(superposition,[],[f171,f215])).

fof(f171,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f276,plain,
    ( spl3_11
    | ~ spl3_10
    | ~ spl3_9
    | spl3_30
    | ~ spl3_31
    | ~ spl3_32
    | ~ spl3_33
    | spl3_35
    | ~ spl3_14
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f272,f214,f157,f274,f265,f261,f257,f253,f121,f126,f131])).

fof(f126,plain,
    ( spl3_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f121,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f157,plain,
    ( spl3_14
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f272,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X1)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_14
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f250,f215])).

% (22101)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f250,plain,
    ( ! [X1] :
        ( ~ r1_waybel_7(sK0,sK1,X1)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_14 ),
    inference(superposition,[],[f67,f159])).

fof(f159,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
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
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

fof(f271,plain,
    ( spl3_11
    | ~ spl3_10
    | ~ spl3_9
    | spl3_30
    | ~ spl3_31
    | ~ spl3_32
    | ~ spl3_33
    | spl3_34
    | ~ spl3_14
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f251,f214,f157,f269,f265,f261,f257,f253,f121,f126,f131])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r1_waybel_7(sK0,sK1,X0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_14
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f249,f215])).

fof(f249,plain,
    ( ! [X0] :
        ( r1_waybel_7(sK0,sK1,X0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_14 ),
    inference(superposition,[],[f66,f159])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f242,plain,
    ( spl3_11
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f232,f214,f162,f143,f131])).

fof(f162,plain,
    ( spl3_15
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f232,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_26 ),
    inference(superposition,[],[f68,f215])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f241,plain,
    ( spl3_28
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f231,f214,f91,f238])).

fof(f91,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f231,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f93,f215])).

fof(f93,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f236,plain,
    ( spl3_24
    | ~ spl3_26
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f230,f219,f214,f206])).

fof(f219,plain,
    ( spl3_27
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f230,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_26
    | ~ spl3_27 ),
    inference(backward_demodulation,[],[f220,f215])).

fof(f220,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f219])).

fof(f228,plain,
    ( ~ spl3_9
    | ~ spl3_25
    | spl3_26
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f227,f219,f138,f214,f210,f121])).

fof(f210,plain,
    ( spl3_25
  <=> v1_tops_1(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f138,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f227,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f225,f140])).

fof(f140,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f225,plain,
    ( ~ v1_tops_1(k2_struct_0(sK0),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_27 ),
    inference(resolution,[],[f220,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f224,plain,
    ( ~ spl3_13
    | spl3_27 ),
    inference(avatar_split_clause,[],[f223,f219,f143])).

fof(f223,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_27 ),
    inference(resolution,[],[f221,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f221,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f219])).

fof(f222,plain,
    ( ~ spl3_9
    | ~ spl3_27
    | spl3_25
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f203,f138,f210,f219,f121])).

fof(f203,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_12 ),
    inference(trivial_inequality_removal,[],[f202])).

fof(f202,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_12 ),
    inference(superposition,[],[f62,f140])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f182,plain,
    ( spl3_15
    | spl3_8
    | ~ spl3_6
    | ~ spl3_5
    | spl3_19
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f153,f96,f180,f101,f106,f116,f162])).

fof(f116,plain,
    ( spl3_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f106,plain,
    ( spl3_6
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f101,plain,
    ( spl3_5
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f96,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f153,plain,
    ( ! [X5] :
        ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ l1_struct_0(X5)
        | v2_struct_0(X5) )
    | ~ spl3_4 ),
    inference(resolution,[],[f98,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f178,plain,
    ( spl3_15
    | spl3_8
    | ~ spl3_6
    | ~ spl3_5
    | spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f152,f96,f166,f101,f106,f116,f162])).

fof(f152,plain,
    ( ! [X4] :
        ( ~ v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4)))
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ l1_struct_0(X4)
        | v2_struct_0(X4) )
    | ~ spl3_4 ),
    inference(resolution,[],[f98,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f177,plain,
    ( spl3_15
    | spl3_8
    | ~ spl3_6
    | ~ spl3_5
    | spl3_18
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f151,f96,f175,f101,f106,f116,f162])).

fof(f151,plain,
    ( ! [X3] :
        ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ l1_struct_0(X3)
        | v2_struct_0(X3) )
    | ~ spl3_4 ),
    inference(resolution,[],[f98,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f172,plain,
    ( spl3_15
    | spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_17
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f149,f96,f170,f101,f106,f111,f116,f162])).

fof(f111,plain,
    ( spl3_7
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f149,plain,
    ( ! [X1] :
        ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1) )
    | ~ spl3_4 ),
    inference(resolution,[],[f98,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f160,plain,
    ( spl3_11
    | ~ spl3_13
    | spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_14
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f147,f96,f157,f101,f106,f111,f116,f143,f131])).

fof(f147,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f98,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f146,plain,
    ( spl3_13
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f136,f121,f143])).

fof(f136,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f123,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f123,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f141,plain,
    ( spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f135,f121,f138])).

fof(f135,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl3_9 ),
    inference(resolution,[],[f123,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f134,plain,(
    ~ spl3_11 ),
    inference(avatar_split_clause,[],[f45,f131])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ r1_waybel_7(sK0,sK1,sK2)
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
    & ( r1_waybel_7(sK0,sK1,sK2)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_7(X0,X1,X2)
                  | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & ( r1_waybel_7(X0,X1,X2)
                  | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(sK0,X1,X2)
                | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
              & ( r1_waybel_7(sK0,X1,X2)
                | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_waybel_7(sK0,X1,X2)
              | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
            & ( r1_waybel_7(sK0,X1,X2)
              | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ~ r1_waybel_7(sK0,sK1,X2)
            | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
          & ( r1_waybel_7(sK0,sK1,X2)
            | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ( ~ r1_waybel_7(sK0,sK1,X2)
          | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
        & ( r1_waybel_7(sK0,sK1,X2)
          | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_waybel_7(sK0,sK1,sK2)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
      & ( r1_waybel_7(sK0,sK1,sK2)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).

fof(f129,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f46,f126])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f124,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f47,f121])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f119,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f48,f116])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f114,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f49,f111])).

fof(f49,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f50,f106])).

fof(f50,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f51,f101])).

fof(f51,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f52,f96])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f53,f91])).

fof(f53,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f54,f85,f81])).

fof(f54,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f55,f85,f81])).

fof(f55,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:03:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (22105)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (22095)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (22106)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (22109)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (22106)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f302,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f88,f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f141,f146,f160,f172,f177,f178,f182,f222,f224,f228,f236,f241,f242,f271,f276,f284,f289,f292,f295,f299,f301])).
% 0.21/0.47  fof(f301,plain,(
% 0.21/0.47    spl3_2 | ~spl3_28 | ~spl3_1 | ~spl3_34),
% 0.21/0.47    inference(avatar_split_clause,[],[f300,f269,f81,f238,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl3_2 <=> r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    spl3_28 <=> m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl3_1 <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f269,plain,(
% 0.21/0.47    spl3_34 <=> ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r1_waybel_7(sK0,sK1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.47  fof(f300,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | (~spl3_1 | ~spl3_34)),
% 0.21/0.47    inference(resolution,[],[f82,f270])).
% 0.21/0.47  fof(f270,plain,(
% 0.21/0.47    ( ! [X0] : (~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,X0)) ) | ~spl3_34),
% 0.21/0.47    inference(avatar_component_clause,[],[f269])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f299,plain,(
% 0.21/0.47    ~spl3_2 | ~spl3_28 | spl3_1 | ~spl3_35),
% 0.21/0.47    inference(avatar_split_clause,[],[f296,f274,f81,f238,f85])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    spl3_35 <=> ! [X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | ~r1_waybel_7(sK0,sK1,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.47  fof(f296,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,sK2) | (spl3_1 | ~spl3_35)),
% 0.21/0.47    inference(resolution,[],[f275,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    ( ! [X1] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | ~m1_subset_1(X1,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,X1)) ) | ~spl3_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f274])).
% 0.21/0.47  fof(f295,plain,(
% 0.21/0.47    ~spl3_13 | spl3_11 | ~spl3_24 | ~spl3_16 | ~spl3_26 | ~spl3_30),
% 0.21/0.47    inference(avatar_split_clause,[],[f294,f253,f214,f166,f206,f131,f143])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    spl3_13 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    spl3_11 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    spl3_24 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    spl3_16 <=> ! [X0] : (~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    spl3_26 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    spl3_30 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.47  fof(f294,plain,(
% 0.21/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | (~spl3_16 | ~spl3_26 | ~spl3_30)),
% 0.21/0.47    inference(forward_demodulation,[],[f293,f215])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f214])).
% 0.21/0.47  fof(f293,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_16 | ~spl3_30)),
% 0.21/0.47    inference(resolution,[],[f255,f167])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f166])).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_30),
% 0.21/0.47    inference(avatar_component_clause,[],[f253])).
% 0.21/0.47  fof(f292,plain,(
% 0.21/0.47    ~spl3_13 | spl3_11 | ~spl3_24 | ~spl3_18 | ~spl3_26 | spl3_33),
% 0.21/0.47    inference(avatar_split_clause,[],[f291,f265,f214,f175,f206,f131,f143])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    spl3_18 <=> ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | v2_struct_0(X3) | ~l1_struct_0(X3) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    spl3_33 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | (~spl3_18 | ~spl3_26 | spl3_33)),
% 0.21/0.47    inference(forward_demodulation,[],[f290,f215])).
% 0.21/0.47  fof(f290,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_18 | spl3_33)),
% 0.21/0.47    inference(resolution,[],[f176,f267])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | spl3_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f265])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | v2_struct_0(X3) | ~l1_struct_0(X3) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))) ) | ~spl3_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f175])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    spl3_31 | ~spl3_13 | spl3_11 | ~spl3_24 | ~spl3_19 | ~spl3_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f286,f214,f180,f206,f131,f143,f257])).
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    spl3_31 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    spl3_19 <=> ! [X5] : (v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) | v2_struct_0(X5) | ~l1_struct_0(X5) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f286,plain,(
% 0.21/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl3_19 | ~spl3_26)),
% 0.21/0.47    inference(superposition,[],[f181,f215])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    ( ! [X5] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | v2_struct_0(X5) | ~l1_struct_0(X5) | v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))) ) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f180])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    spl3_32 | ~spl3_13 | spl3_11 | ~spl3_24 | ~spl3_17 | ~spl3_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f281,f214,f170,f206,f131,f143,f261])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    spl3_32 <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    spl3_17 <=> ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl3_17 | ~spl3_26)),
% 0.21/0.47    inference(superposition,[],[f171,f215])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    ( ! [X1] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1) | ~l1_struct_0(X1) | v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))) ) | ~spl3_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f170])).
% 0.21/0.47  fof(f276,plain,(
% 0.21/0.47    spl3_11 | ~spl3_10 | ~spl3_9 | spl3_30 | ~spl3_31 | ~spl3_32 | ~spl3_33 | spl3_35 | ~spl3_14 | ~spl3_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f272,f214,f157,f274,f265,f261,f257,f253,f121,f126,f131])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    spl3_10 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl3_9 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    spl3_14 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f272,plain,(
% 0.21/0.47    ( ! [X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,X1) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl3_14 | ~spl3_26)),
% 0.21/0.47    inference(forward_demodulation,[],[f250,f215])).
% 0.21/0.47  % (22101)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  fof(f250,plain,(
% 0.21/0.47    ( ! [X1] : (~r1_waybel_7(sK0,sK1,X1) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl3_14),
% 0.21/0.47    inference(superposition,[],[f67,f159])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f157])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    spl3_11 | ~spl3_10 | ~spl3_9 | spl3_30 | ~spl3_31 | ~spl3_32 | ~spl3_33 | spl3_34 | ~spl3_14 | ~spl3_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f251,f214,f157,f269,f265,f261,f257,f253,f121,f126,f131])).
% 0.21/0.47  fof(f251,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,X0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl3_14 | ~spl3_26)),
% 0.21/0.47    inference(forward_demodulation,[],[f249,f215])).
% 0.21/0.47  fof(f249,plain,(
% 0.21/0.47    ( ! [X0] : (r1_waybel_7(sK0,sK1,X0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl3_14),
% 0.21/0.47    inference(superposition,[],[f66,f159])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    spl3_11 | ~spl3_13 | ~spl3_15 | ~spl3_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f232,f214,f162,f143,f131])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    spl3_15 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_26),
% 0.21/0.47    inference(superposition,[],[f68,f215])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.47  fof(f241,plain,(
% 0.21/0.47    spl3_28 | ~spl3_3 | ~spl3_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f231,f214,f91,f238])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl3_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_26)),
% 0.21/0.47    inference(backward_demodulation,[],[f93,f215])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f91])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    spl3_24 | ~spl3_26 | ~spl3_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f230,f219,f214,f206])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    spl3_27 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_26 | ~spl3_27)),
% 0.21/0.47    inference(backward_demodulation,[],[f220,f215])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f219])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    ~spl3_9 | ~spl3_25 | spl3_26 | ~spl3_12 | ~spl3_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f227,f219,f138,f214,f210,f121])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    spl3_25 <=> v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    spl3_12 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | ~v1_tops_1(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | (~spl3_12 | ~spl3_27)),
% 0.21/0.47    inference(forward_demodulation,[],[f225,f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f138])).
% 0.21/0.47  fof(f225,plain,(
% 0.21/0.47    ~v1_tops_1(k2_struct_0(sK0),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~spl3_27),
% 0.21/0.47    inference(resolution,[],[f220,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    ~spl3_13 | spl3_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f223,f219,f143])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    ~l1_struct_0(sK0) | spl3_27),
% 0.21/0.47    inference(resolution,[],[f221,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f219])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    ~spl3_9 | ~spl3_27 | spl3_25 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f203,f138,f210,f219,f121])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    v1_tops_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_12),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f202])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_12),
% 0.21/0.47    inference(superposition,[],[f62,f140])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    spl3_15 | spl3_8 | ~spl3_6 | ~spl3_5 | spl3_19 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f153,f96,f180,f101,f106,f116,f162])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl3_8 <=> v1_xboole_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl3_6 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl3_5 <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ( ! [X5] : (v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X5) | v2_struct_0(X5)) ) | ~spl3_4),
% 0.21/0.47    inference(resolution,[],[f98,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v4_orders_2(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    spl3_15 | spl3_8 | ~spl3_6 | ~spl3_5 | spl3_16 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f152,f96,f166,f101,f106,f116,f162])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X4] : (~v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X4) | v2_struct_0(X4)) ) | ~spl3_4),
% 0.21/0.47    inference(resolution,[],[f98,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    spl3_15 | spl3_8 | ~spl3_6 | ~spl3_5 | spl3_18 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f151,f96,f175,f101,f106,f116,f162])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) ) | ~spl3_4),
% 0.21/0.47    inference(resolution,[],[f98,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    spl3_15 | spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_17 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f149,f96,f170,f101,f106,f111,f116,f162])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl3_7 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X1) | v2_struct_0(X1)) ) | ~spl3_4),
% 0.21/0.47    inference(resolution,[],[f98,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    spl3_11 | ~spl3_13 | spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_14 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f147,f96,f157,f101,f106,f111,f116,f143,f131])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_4),
% 0.21/0.47    inference(resolution,[],[f98,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    spl3_13 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f136,f121,f143])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl3_9),
% 0.21/0.47    inference(resolution,[],[f123,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f121])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl3_12 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f135,f121,f138])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl3_9),
% 0.21/0.47    inference(resolution,[],[f123,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f131])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(sK0,sK1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & (r1_waybel_7(sK0,sK1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ? [X2] : ((~r1_waybel_7(sK0,sK1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & (r1_waybel_7(sK0,sK1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f15])).
% 0.21/0.47  fof(f15,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f46,f126])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f121])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ~spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f48,f116])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~v1_xboole_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f49,f111])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f106])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f101])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f52,f96])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f53,f91])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f54,f85,f81])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f55,f85,f81])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22106)------------------------------
% 0.21/0.47  % (22106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22106)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22106)Memory used [KB]: 10874
% 0.21/0.47  % (22106)Time elapsed: 0.055 s
% 0.21/0.47  % (22106)------------------------------
% 0.21/0.47  % (22106)------------------------------
% 0.21/0.47  % (22099)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (22098)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (22094)Success in time 0.122 s
%------------------------------------------------------------------------------
