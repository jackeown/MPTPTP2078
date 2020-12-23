%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 368 expanded)
%              Number of leaves         :   38 ( 177 expanded)
%              Depth                    :    9
%              Number of atoms          :  806 (1663 expanded)
%              Number of equality atoms :   16 (  81 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f104,f109,f114,f119,f128,f129,f135,f141,f147,f184,f195,f210,f212,f219,f221,f228,f235,f242,f256,f259,f301,f303,f307])).

fof(f307,plain,
    ( spl4_3
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_24
    | spl4_27
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_14
    | spl4_11
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f306,f239,f138,f121,f125,f144,f81,f76,f232,f207,f250,f246,f86])).

fof(f86,plain,
    ( spl4_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f246,plain,
    ( spl4_29
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f250,plain,
    ( spl4_30
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f207,plain,
    ( spl4_24
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f232,plain,
    ( spl4_27
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f76,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f81,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f144,plain,
    ( spl4_14
  <=> m1_subset_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f125,plain,
    ( spl4_11
  <=> r1_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f121,plain,
    ( spl4_10
  <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f138,plain,
    ( spl4_13
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f239,plain,
    ( spl4_28
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f306,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f305,f241])).

fof(f241,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f239])).

fof(f305,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v2_struct_0(sK0)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f304,f140])).

fof(f140,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f304,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v2_struct_0(sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f122,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

fof(f122,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f303,plain,
    ( ~ spl4_14
    | spl4_10
    | ~ spl4_11
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f302,f254,f125,f121,f144])).

fof(f254,plain,
    ( spl4_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ r1_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f302,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_11
    | ~ spl4_31 ),
    inference(resolution,[],[f255,f126])).

fof(f126,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f254])).

fof(f301,plain,
    ( spl4_22
    | ~ spl4_7
    | spl4_8
    | ~ spl4_6
    | ~ spl4_5
    | ~ spl4_23
    | spl4_30
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f299,f226,f91,f250,f203,f96,f101,f111,f106,f199])).

fof(f199,plain,
    ( spl4_22
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f106,plain,
    ( spl4_7
  <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f111,plain,
    ( spl4_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

% (13770)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f101,plain,
    ( spl4_6
  <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f96,plain,
    ( spl4_5
  <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f203,plain,
    ( spl4_23
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f91,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f226,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v7_waybel_0(k3_yellow19(sK0,X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f299,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(resolution,[],[f227,f93])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | v7_waybel_0(k3_yellow19(sK0,X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
        | v1_xboole_0(X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f259,plain,
    ( spl4_22
    | ~ spl4_6
    | spl4_8
    | ~ spl4_5
    | ~ spl4_23
    | spl4_29
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f257,f217,f91,f246,f203,f96,f111,f101,f199])).

fof(f217,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f257,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(resolution,[],[f218,f93])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f217])).

fof(f256,plain,
    ( spl4_3
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_24
    | spl4_27
    | ~ spl4_1
    | ~ spl4_2
    | spl4_31
    | ~ spl4_13
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f244,f239,f138,f254,f81,f76,f232,f207,f250,f246,f86])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | ~ spl4_13
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f243,f140])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | ~ spl4_28 ),
    inference(superposition,[],[f49,f241])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f242,plain,
    ( spl4_28
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f236,f91,f132,f111,f106,f101,f96,f86,f239])).

fof(f132,plain,
    ( spl4_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f236,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v2_struct_0(sK0)
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f68,f93])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v2_struct_0(X0)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(definition_unfolding,[],[f52,f46,f46,f46,f46])).

fof(f46,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f235,plain,
    ( spl4_22
    | ~ spl4_6
    | spl4_8
    | ~ spl4_5
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f229,f193,f91,f232,f203,f96,f111,f101,f199])).

fof(f193,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_struct_0(k3_yellow19(sK0,X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f229,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(resolution,[],[f194,f93])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | ~ v2_struct_0(k3_yellow19(sK0,X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f228,plain,
    ( spl4_3
    | ~ spl4_12
    | spl4_26
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f224,f138,f226,f132,f86])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | v1_xboole_0(X0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | v7_waybel_0(k3_yellow19(sK0,X0,X1)) )
    | ~ spl4_13 ),
    inference(superposition,[],[f73,f140])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f63,f46,f46,f46,f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
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
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
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

fof(f221,plain,
    ( spl4_3
    | ~ spl4_12
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f220,f199,f132,f86])).

fof(f220,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_22 ),
    inference(resolution,[],[f201,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f201,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f199])).

fof(f219,plain,
    ( spl4_3
    | ~ spl4_12
    | spl4_25
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f215,f138,f217,f132,f86])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | v1_xboole_0(X0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0) )
    | ~ spl4_13 ),
    inference(superposition,[],[f71,f140])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f61,f46,f46,f46])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
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

fof(f212,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl4_23 ),
    inference(resolution,[],[f205,f157])).

fof(f157,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f156,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f156,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f205,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f210,plain,
    ( spl4_22
    | ~ spl4_6
    | spl4_8
    | ~ spl4_5
    | ~ spl4_23
    | spl4_24
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f196,f182,f91,f207,f203,f96,f111,f101,f199])).

fof(f182,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_orders_2(k3_yellow19(sK0,X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f196,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(resolution,[],[f183,f93])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | v4_orders_2(k3_yellow19(sK0,X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | v1_xboole_0(X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f195,plain,
    ( spl4_3
    | ~ spl4_12
    | spl4_21
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f187,f138,f193,f132,f86])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | v1_xboole_0(X0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | ~ v2_struct_0(k3_yellow19(sK0,X0,X1)) )
    | ~ spl4_13 ),
    inference(superposition,[],[f70,f140])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f58,f46,f46,f46])).

% (13768)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

% (13772)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
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
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
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

fof(f184,plain,
    ( spl4_3
    | ~ spl4_12
    | spl4_19
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f168,f138,f182,f132,f86])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | v1_xboole_0(X0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
        | v4_orders_2(k3_yellow19(sK0,X0,X1)) )
    | ~ spl4_13 ),
    inference(superposition,[],[f69,f140])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v4_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f59,f46,f46,f46])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v4_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f147,plain,
    ( spl4_14
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f142,f138,f116,f144])).

fof(f116,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f142,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f118,f140])).

fof(f118,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f141,plain,
    ( spl4_13
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f136,f132,f138])).

fof(f136,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f48,f134])).

fof(f134,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f135,plain,
    ( spl4_12
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f130,f76,f132])).

fof(f130,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f47,f78])).

fof(f78,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f129,plain,
    ( spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f35,f125,f121])).

fof(f35,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f128,plain,
    ( ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f36,f125,f121])).

fof(f36,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f37,f116])).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f114,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f38,f111])).

fof(f38,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f67,f106])).

fof(f67,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f39,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f66,f101])).

fof(f66,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f40,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f65,f96])).

fof(f65,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f41,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f64,f91])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f43,f86])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f81])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f45,f76])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (13766)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (13765)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (13750)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (13755)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (13753)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (13754)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (13751)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (13758)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (13752)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (13777)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (13773)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (13757)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (13766)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (13758)Refutation not found, incomplete strategy% (13758)------------------------------
% 0.21/0.52  % (13758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13758)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13758)Memory used [KB]: 10746
% 0.21/0.52  % (13758)Time elapsed: 0.107 s
% 0.21/0.52  % (13758)------------------------------
% 0.21/0.52  % (13758)------------------------------
% 0.21/0.53  % (13762)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (13764)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f308,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f104,f109,f114,f119,f128,f129,f135,f141,f147,f184,f195,f210,f212,f219,f221,f228,f235,f242,f256,f259,f301,f303,f307])).
% 0.21/0.53  fof(f307,plain,(
% 0.21/0.53    spl4_3 | ~spl4_29 | ~spl4_30 | ~spl4_24 | spl4_27 | ~spl4_1 | ~spl4_2 | ~spl4_14 | spl4_11 | ~spl4_10 | ~spl4_13 | ~spl4_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f306,f239,f138,f121,f125,f144,f81,f76,f232,f207,f250,f246,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl4_3 <=> v2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    spl4_29 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    spl4_30 <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    spl4_24 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    spl4_27 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    spl4_1 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    spl4_14 <=> m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl4_11 <=> r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl4_10 <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl4_13 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    spl4_28 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.53  fof(f306,plain,(
% 0.21/0.53    r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(sK0) | (~spl4_10 | ~spl4_13 | ~spl4_28)),
% 0.21/0.53    inference(forward_demodulation,[],[f305,f241])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl4_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f239])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v2_struct_0(sK0) | (~spl4_10 | ~spl4_13)),
% 0.21/0.53    inference(forward_demodulation,[],[f304,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl4_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f138])).
% 0.21/0.53  fof(f304,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v2_struct_0(sK0) | ~spl4_10),
% 0.21/0.53    inference(resolution,[],[f122,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~spl4_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    ~spl4_14 | spl4_10 | ~spl4_11 | ~spl4_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f302,f254,f125,f121,f144])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    spl4_31 <=> ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~r1_waybel_7(sK0,sK1,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_11 | ~spl4_31)),
% 0.21/0.53    inference(resolution,[],[f255,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    r1_waybel_7(sK0,sK1,sK2) | ~spl4_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl4_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f254])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    spl4_22 | ~spl4_7 | spl4_8 | ~spl4_6 | ~spl4_5 | ~spl4_23 | spl4_30 | ~spl4_4 | ~spl4_26),
% 0.21/0.53    inference(avatar_split_clause,[],[f299,f226,f91,f250,f203,f96,f101,f111,f106,f199])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    spl4_22 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl4_7 <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl4_8 <=> v1_xboole_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.53  % (13770)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl4_6 <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl4_5 <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    spl4_23 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    spl4_26 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v7_waybel_0(k3_yellow19(sK0,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(k2_struct_0(sK0)) | (~spl4_4 | ~spl4_26)),
% 0.21/0.53    inference(resolution,[],[f227,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f91])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v7_waybel_0(k3_yellow19(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X0)) ) | ~spl4_26),
% 0.21/0.53    inference(avatar_component_clause,[],[f226])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    spl4_22 | ~spl4_6 | spl4_8 | ~spl4_5 | ~spl4_23 | spl4_29 | ~spl4_4 | ~spl4_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f257,f217,f91,f246,f203,f96,f111,f101,f199])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    spl4_25 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0)) | (~spl4_4 | ~spl4_25)),
% 0.21/0.53    inference(resolution,[],[f218,f93])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0)) ) | ~spl4_25),
% 0.21/0.53    inference(avatar_component_clause,[],[f217])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    spl4_3 | ~spl4_29 | ~spl4_30 | ~spl4_24 | spl4_27 | ~spl4_1 | ~spl4_2 | spl4_31 | ~spl4_13 | ~spl4_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f244,f239,f138,f254,f81,f76,f232,f207,f250,f246,f86])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(sK0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (~spl4_13 | ~spl4_28)),
% 0.21/0.53    inference(forward_demodulation,[],[f243,f140])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | ~spl4_28),
% 0.21/0.53    inference(superposition,[],[f49,f241])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_waybel_9(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    spl4_28 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_12 | ~spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f236,f91,f132,f111,f106,f101,f96,f86,f239])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl4_12 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v2_struct_0(sK0) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl4_4),
% 0.21/0.53    inference(resolution,[],[f68,f93])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v2_struct_0(X0) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f52,f46,f46,f46,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    spl4_22 | ~spl4_6 | spl4_8 | ~spl4_5 | ~spl4_23 | ~spl4_27 | ~spl4_4 | ~spl4_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f229,f193,f91,f232,f203,f96,f111,f101,f199])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    spl4_21 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_struct_0(k3_yellow19(sK0,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0)) | (~spl4_4 | ~spl4_21)),
% 0.21/0.53    inference(resolution,[],[f194,f93])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v2_struct_0(k3_yellow19(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0)) ) | ~spl4_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f193])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    spl4_3 | ~spl4_12 | spl4_26 | ~spl4_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f224,f138,f226,f132,f86])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | v1_xboole_0(X0) | v2_struct_0(sK0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v7_waybel_0(k3_yellow19(sK0,X0,X1))) ) | ~spl4_13),
% 0.21/0.53    inference(superposition,[],[f73,f140])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v7_waybel_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f63,f46,f46,f46,f46])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v7_waybel_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    spl4_3 | ~spl4_12 | ~spl4_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f220,f199,f132,f86])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_22),
% 0.21/0.53    inference(resolution,[],[f201,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    v1_xboole_0(k2_struct_0(sK0)) | ~spl4_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f199])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    spl4_3 | ~spl4_12 | spl4_25 | ~spl4_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f215,f138,f217,f132,f86])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | v1_xboole_0(X0) | v2_struct_0(sK0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0)) ) | ~spl4_13),
% 0.21/0.53    inference(superposition,[],[f71,f140])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f61,f46,f46,f46])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    spl4_23),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    $false | spl4_23),
% 0.21/0.53    inference(resolution,[],[f205,f157])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(resolution,[],[f156,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f155])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f55,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl4_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f203])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    spl4_22 | ~spl4_6 | spl4_8 | ~spl4_5 | ~spl4_23 | spl4_24 | ~spl4_4 | ~spl4_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f196,f182,f91,f207,f203,f96,f111,f101,f199])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    spl4_19 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_orders_2(k3_yellow19(sK0,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0)) | (~spl4_4 | ~spl4_19)),
% 0.21/0.53    inference(resolution,[],[f183,f93])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v4_orders_2(k3_yellow19(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0)) ) | ~spl4_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f182])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    spl4_3 | ~spl4_12 | spl4_21 | ~spl4_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f187,f138,f193,f132,f86])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | v1_xboole_0(X0) | v2_struct_0(sK0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v2_struct_0(k3_yellow19(sK0,X0,X1))) ) | ~spl4_13),
% 0.21/0.53    inference(superposition,[],[f70,f140])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v2_struct_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f58,f46,f46,f46])).
% 0.21/0.53  % (13768)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  % (13772)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    spl4_3 | ~spl4_12 | spl4_19 | ~spl4_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f168,f138,f182,f132,f86])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | v1_xboole_0(X0) | v2_struct_0(sK0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v4_orders_2(k3_yellow19(sK0,X0,X1))) ) | ~spl4_13),
% 0.21/0.53    inference(superposition,[],[f69,f140])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v4_orders_2(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f59,f46,f46,f46])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v4_orders_2(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    spl4_14 | ~spl4_9 | ~spl4_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f142,f138,f116,f144])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl4_9 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_9 | ~spl4_13)),
% 0.21/0.53    inference(backward_demodulation,[],[f118,f140])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f116])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    spl4_13 | ~spl4_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f136,f132,f138])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl4_12),
% 0.21/0.53    inference(resolution,[],[f48,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl4_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    spl4_12 | ~spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f130,f76,f132])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl4_1),
% 0.21/0.53    inference(resolution,[],[f47,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f76])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl4_10 | spl4_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f125,f121])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~spl4_10 | ~spl4_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f125,f121])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f116])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~spl4_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f38,f111])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl4_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f67,f106])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f46])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f66,f101])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f46])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f65,f96])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f46])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f64,f91])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f46])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f86])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f81])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f76])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (13766)------------------------------
% 0.21/0.53  % (13766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13766)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (13766)Memory used [KB]: 11001
% 0.21/0.53  % (13766)Time elapsed: 0.118 s
% 0.21/0.53  % (13766)------------------------------
% 0.21/0.53  % (13766)------------------------------
% 0.21/0.53  % (13775)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (13774)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (13754)Refutation not found, incomplete strategy% (13754)------------------------------
% 0.21/0.54  % (13754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13754)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13754)Memory used [KB]: 6396
% 0.21/0.54  % (13754)Time elapsed: 0.111 s
% 0.21/0.54  % (13754)------------------------------
% 0.21/0.54  % (13754)------------------------------
% 0.21/0.54  % (13749)Success in time 0.179 s
%------------------------------------------------------------------------------
