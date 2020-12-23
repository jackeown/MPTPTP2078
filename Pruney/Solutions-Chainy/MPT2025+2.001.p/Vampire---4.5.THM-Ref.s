%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 333 expanded)
%              Number of leaves         :   25 ( 123 expanded)
%              Depth                    :   30
%              Number of atoms          :  979 (1919 expanded)
%              Number of equality atoms :   21 (  70 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f95,f100,f105,f110,f116,f126,f147,f159,f182,f224])).

fof(f224,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f222,f69])).

fof(f69,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f222,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f221,f89])).

fof(f89,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f221,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f220,f79])).

fof(f79,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f219,f74])).

fof(f74,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f219,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f218,f94])).

fof(f94,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f218,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f217,f99])).

fof(f99,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_10
  <=> r2_hidden(sK1,k2_pre_topc(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

% (24602)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f217,plain,
    ( r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(resolution,[],[f208,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK4(X0,X1,X2),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_connsp_2)).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK4(sK0,X0,sK1),sK3)
        | r2_hidden(sK1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(resolution,[],[f207,f142])).

fof(f142,plain,
    ( ! [X3] :
        ( ~ r1_waybel_0(sK0,sK2,X3)
        | ~ r1_xboole_0(X3,sK3) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f141,f69])).

fof(f141,plain,
    ( ! [X3] :
        ( ~ r1_waybel_0(sK0,sK2,X3)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(X3,sK3) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f140,f84])).

fof(f84,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl8_7
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f140,plain,
    ( ! [X3] :
        ( ~ l1_waybel_0(sK2,sK0)
        | ~ r1_waybel_0(sK0,sK2,X3)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(X3,sK3) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f139,f64])).

fof(f64,plain,
    ( v7_waybel_0(sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl8_3
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f139,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ r1_waybel_0(sK0,sK2,X3)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(X3,sK3) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f138,f59])).

fof(f59,plain,
    ( v4_orders_2(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl8_2
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f138,plain,
    ( ! [X3] :
        ( ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ r1_waybel_0(sK0,sK2,X3)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(X3,sK3) )
    | spl8_1
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f137,f54])).

fof(f54,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f137,plain,
    ( ! [X3] :
        ( v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ r1_waybel_0(sK0,sK2,X3)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(X3,sK3) )
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f135,f115])).

fof(f115,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_13
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f135,plain,
    ( ! [X3] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ r1_waybel_0(sK0,sK2,X3)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(X3,sK3) )
    | ~ spl8_14 ),
    inference(resolution,[],[f35,f125])).

fof(f125,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_14
  <=> r1_waybel_0(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_0(X0,X1,X3)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

fof(f207,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1,k2_pre_topc(sK0,X0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f206,f69])).

fof(f206,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | r2_hidden(sK1,k2_pre_topc(sK0,X0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f205,f89])).

% (24605)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f205,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(sK1,k2_pre_topc(sK0,X0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f204,f79])).

fof(f204,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(sK1,k2_pre_topc(sK0,X0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f202,f74])).

fof(f202,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(sK1,k2_pre_topc(sK0,X0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(resolution,[],[f201,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK4(X0,X1,X2),X0,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | r1_waybel_0(sK0,sK2,X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f200,f89])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | r1_waybel_0(sK0,sK2,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(resolution,[],[f199,f104])).

fof(f104,plain,
    ( r2_hidden(sK1,k10_yellow_6(sK0,sK2))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_11
  <=> r2_hidden(sK1,k10_yellow_6(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK2))
        | ~ m1_connsp_2(X1,sK0,X0)
        | r1_waybel_0(sK0,sK2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f198,f69])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | r1_waybel_0(sK0,sK2,X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f197,f84])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | r1_waybel_0(sK0,sK2,X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f196,f64])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | r1_waybel_0(sK0,sK2,X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f195,f59])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | r1_waybel_0(sK0,sK2,X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f194,f54])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | r1_waybel_0(sK0,sK2,X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f193,f79])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | r1_waybel_0(sK0,sK2,X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f192,f74])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | r1_waybel_0(sK0,sK2,X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl8_15 ),
    inference(resolution,[],[f50,f146])).

fof(f146,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_15
  <=> m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f50,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_connsp_2(X4,X0,X3)
      | r1_waybel_0(X0,X1,X4)
      | ~ r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_connsp_2(X4,X0,X3)
      | r1_waybel_0(X0,X1,X4)
      | ~ r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f182,plain,
    ( spl8_17
    | spl8_18
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f173,f92,f82,f77,f72,f67,f62,f57,f52,f179,f175])).

fof(f175,plain,
    ( spl8_17
  <=> sK3 = k10_yellow_6(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f179,plain,
    ( spl8_18
  <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f173,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | sK3 = k10_yellow_6(sK0,sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f172,f54])).

fof(f172,plain,
    ( v2_struct_0(sK2)
    | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | sK3 = k10_yellow_6(sK0,sK2)
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f171,f64])).

fof(f171,plain,
    ( ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | sK3 = k10_yellow_6(sK0,sK2)
    | ~ spl8_2
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f170,f59])).

fof(f170,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | sK3 = k10_yellow_6(sK0,sK2)
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(resolution,[],[f166,f84])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | v2_struct_0(X0)
        | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0))
        | sK3 = k10_yellow_6(sK0,X0) )
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f165,f69])).

fof(f165,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0)
        | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0))
        | sK3 = k10_yellow_6(sK0,X0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f164,f79])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0)
        | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0))
        | sK3 = k10_yellow_6(sK0,X0) )
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f162,f74])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0)
        | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0))
        | sK3 = k10_yellow_6(sK0,X0) )
    | ~ spl8_9 ),
    inference(resolution,[],[f46,f94])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | k10_yellow_6(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f159,plain,
    ( ~ spl8_16
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f148,f123,f113,f82,f67,f62,f57,f52,f156])).

fof(f156,plain,
    ( spl8_16
  <=> r1_xboole_0(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f148,plain,
    ( ~ r1_xboole_0(sK3,sK3)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(resolution,[],[f142,f125])).

fof(f147,plain,
    ( spl8_15
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f133,f82,f77,f72,f67,f62,f57,f52,f144])).

fof(f133,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f132,f69])).

fof(f132,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f131,f64])).

fof(f131,plain,
    ( ~ v7_waybel_0(sK2)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f130,f59])).

fof(f130,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,
    ( v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f128,f79])).

fof(f128,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f127,f74])).

fof(f127,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_7 ),
    inference(resolution,[],[f47,f84])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f126,plain,
    ( spl8_14
    | spl8_1
    | spl8_4
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f121,f113,f107,f82,f67,f52,f123])).

fof(f107,plain,
    ( spl8_12
  <=> sK3 = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f121,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | spl8_1
    | spl8_4
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f120,f69])).

fof(f120,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f119,f84])).

fof(f119,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f118,f54])).

fof(f118,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | v2_struct_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f117,f115])).

fof(f117,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12 ),
    inference(superposition,[],[f36,f109])).

fof(f109,plain,
    ( sK3 = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

fof(f116,plain,
    ( spl8_13
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f111,f77,f113])).

fof(f111,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f34,f79])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f110,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f23,f107])).

fof(f23,plain,(
    sK3 = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r2_hidden(X1,k10_yellow_6(X0,X2))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                       => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( r2_hidden(X1,k10_yellow_6(X0,X2))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                     => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_9)).

fof(f105,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f29,f102])).

fof(f29,plain,(
    r2_hidden(sK1,k10_yellow_6(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f100,plain,(
    ~ spl8_10 ),
    inference(avatar_split_clause,[],[f24,f97])).

fof(f24,plain,(
    ~ r2_hidden(sK1,k2_pre_topc(sK0,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f22,f92])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f30,f87])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f28,f82])).

fof(f28,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (24610)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (24608)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (24615)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (24610)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f95,f100,f105,f110,f116,f126,f147,f159,f182,f224])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f223])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    $false | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl8_4 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f221,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl8_8 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f220,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl8_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl8_6 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f219,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl8_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl8_5 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl8_9 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f217,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~r2_hidden(sK1,k2_pre_topc(sK0,sK3)) | spl8_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl8_10 <=> r2_hidden(sK1,k2_pre_topc(sK0,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.49  % (24602)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    r2_hidden(sK1,k2_pre_topc(sK0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    r2_hidden(sK1,k2_pre_topc(sK0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k2_pre_topc(sK0,sK3)) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(resolution,[],[f208,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(sK4(X0,X1,X2),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => ~r1_xboole_0(X3,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_connsp_2)).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(sK4(sK0,X0,sK1),sK3) | r2_hidden(sK1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15)),
% 0.21/0.49    inference(resolution,[],[f207,f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X3] : (~r1_waybel_0(sK0,sK2,X3) | ~r1_xboole_0(X3,sK3)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_7 | ~spl8_13 | ~spl8_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f141,f69])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X3] : (~r1_waybel_0(sK0,sK2,X3) | v2_struct_0(sK0) | ~r1_xboole_0(X3,sK3)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_7 | ~spl8_13 | ~spl8_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f140,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    l1_waybel_0(sK2,sK0) | ~spl8_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl8_7 <=> l1_waybel_0(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X3] : (~l1_waybel_0(sK2,sK0) | ~r1_waybel_0(sK0,sK2,X3) | v2_struct_0(sK0) | ~r1_xboole_0(X3,sK3)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_13 | ~spl8_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f139,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    v7_waybel_0(sK2) | ~spl8_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl8_3 <=> v7_waybel_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X3] : (~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~r1_waybel_0(sK0,sK2,X3) | v2_struct_0(sK0) | ~r1_xboole_0(X3,sK3)) ) | (spl8_1 | ~spl8_2 | ~spl8_13 | ~spl8_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f138,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v4_orders_2(sK2) | ~spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl8_2 <=> v4_orders_2(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X3] : (~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~r1_waybel_0(sK0,sK2,X3) | v2_struct_0(sK0) | ~r1_xboole_0(X3,sK3)) ) | (spl8_1 | ~spl8_13 | ~spl8_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f137,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ~v2_struct_0(sK2) | spl8_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl8_1 <=> v2_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X3] : (v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~r1_waybel_0(sK0,sK2,X3) | v2_struct_0(sK0) | ~r1_xboole_0(X3,sK3)) ) | (~spl8_13 | ~spl8_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f135,f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    l1_struct_0(sK0) | ~spl8_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl8_13 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X3] : (~l1_struct_0(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~r1_waybel_0(sK0,sK2,X3) | v2_struct_0(sK0) | ~r1_xboole_0(X3,sK3)) ) | ~spl8_14),
% 0.21/0.49    inference(resolution,[],[f35,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    r1_waybel_0(sK0,sK2,sK3) | ~spl8_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl8_14 <=> r1_waybel_0(sK0,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_waybel_0(X0,X1,X3) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~r1_waybel_0(X0,X1,X2) | v2_struct_0(X0) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X0] : (r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k2_pre_topc(sK0,X0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f206,f69])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ( ! [X0] : (r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK1,k2_pre_topc(sK0,X0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f205,f89])).
% 0.21/0.49  % (24605)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ( ! [X0] : (r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k2_pre_topc(sK0,X0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f204,f79])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ( ! [X0] : (r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k2_pre_topc(sK0,X0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f202,f74])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    ( ! [X0] : (r1_waybel_0(sK0,sK2,sK4(sK0,X0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k2_pre_topc(sK0,X0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_15)),
% 0.21/0.49    inference(resolution,[],[f201,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(sK4(X0,X1,X2),X0,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | r1_waybel_0(sK0,sK2,X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f200,f89])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | r1_waybel_0(sK0,sK2,X0) | ~m1_subset_1(sK1,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_11 | ~spl8_15)),
% 0.21/0.49    inference(resolution,[],[f199,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    r2_hidden(sK1,k10_yellow_6(sK0,sK2)) | ~spl8_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl8_11 <=> r2_hidden(sK1,k10_yellow_6(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k10_yellow_6(sK0,sK2)) | ~m1_connsp_2(X1,sK0,X0) | r1_waybel_0(sK0,sK2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f198,f69])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | r1_waybel_0(sK0,sK2,X1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f197,f84])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | r1_waybel_0(sK0,sK2,X1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f196,f64])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | r1_waybel_0(sK0,sK2,X1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (spl8_1 | ~spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f195,f59])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | r1_waybel_0(sK0,sK2,X1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (spl8_1 | ~spl8_5 | ~spl8_6 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f194,f54])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | r1_waybel_0(sK0,sK2,X1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (~spl8_5 | ~spl8_6 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f193,f79])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | r1_waybel_0(sK0,sK2,X1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (~spl8_5 | ~spl8_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f192,f74])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | r1_waybel_0(sK0,sK2,X1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | ~spl8_15),
% 0.21/0.49    inference(resolution,[],[f50,f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl8_15 <=> m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_connsp_2(X4,X0,X3) | r1_waybel_0(X0,X1,X4) | ~r2_hidden(X3,k10_yellow_6(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_connsp_2(X4,X0,X3) | r1_waybel_0(X0,X1,X4) | ~r2_hidden(X3,X2) | k10_yellow_6(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl8_17 | spl8_18 | spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f173,f92,f82,f77,f72,f67,f62,f57,f52,f179,f175])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl8_17 <=> sK3 = k10_yellow_6(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl8_18 <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | sK3 = k10_yellow_6(sK0,sK2) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f172,f54])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    v2_struct_0(sK2) | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | sK3 = k10_yellow_6(sK0,sK2) | (~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f171,f64])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~v7_waybel_0(sK2) | v2_struct_0(sK2) | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | sK3 = k10_yellow_6(sK0,sK2) | (~spl8_2 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f170,f59])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | v2_struct_0(sK2) | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | sK3 = k10_yellow_6(sK0,sK2) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_9)),
% 0.21/0.49    inference(resolution,[],[f166,f84])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) | sK3 = k10_yellow_6(sK0,X0)) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f165,f69])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) | sK3 = k10_yellow_6(sK0,X0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f164,f79])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) | sK3 = k10_yellow_6(sK0,X0)) ) | (~spl8_5 | ~spl8_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f162,f74])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) | sK3 = k10_yellow_6(sK0,X0)) ) | ~spl8_9),
% 0.21/0.49    inference(resolution,[],[f46,f94])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | k10_yellow_6(X0,X1) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~spl8_16 | spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_7 | ~spl8_13 | ~spl8_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f148,f123,f113,f82,f67,f62,f57,f52,f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl8_16 <=> r1_xboole_0(sK3,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~r1_xboole_0(sK3,sK3) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_7 | ~spl8_13 | ~spl8_14)),
% 0.21/0.49    inference(resolution,[],[f142,f125])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    spl8_15 | spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f133,f82,f77,f72,f67,f62,f57,f52,f144])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f132,f69])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    v2_struct_0(sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f131,f64])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~v7_waybel_0(sK2) | v2_struct_0(sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl8_1 | ~spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f59])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | v2_struct_0(sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl8_1 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f54])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | v2_struct_0(sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_5 | ~spl8_6 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f128,f79])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | v2_struct_0(sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_5 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f74])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | v2_struct_0(sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_7),
% 0.21/0.49    inference(resolution,[],[f47,f84])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | v2_struct_0(X0) | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl8_14 | spl8_1 | spl8_4 | ~spl8_7 | ~spl8_12 | ~spl8_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f121,f113,f107,f82,f67,f52,f123])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl8_12 <=> sK3 = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    r1_waybel_0(sK0,sK2,sK3) | (spl8_1 | spl8_4 | ~spl8_7 | ~spl8_12 | ~spl8_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f69])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    r1_waybel_0(sK0,sK2,sK3) | v2_struct_0(sK0) | (spl8_1 | ~spl8_7 | ~spl8_12 | ~spl8_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f84])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    r1_waybel_0(sK0,sK2,sK3) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_12 | ~spl8_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f54])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    r1_waybel_0(sK0,sK2,sK3) | v2_struct_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f115])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    r1_waybel_0(sK0,sK2,sK3) | ~l1_struct_0(sK0) | v2_struct_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~spl8_12),
% 0.21/0.49    inference(superposition,[],[f36,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    sK3 = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) | ~spl8_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl8_13 | ~spl8_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f77,f113])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    l1_struct_0(sK0) | ~spl8_6),
% 0.21/0.49    inference(resolution,[],[f34,f79])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl8_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f107])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    sK3 = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_9)).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f102])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    r2_hidden(sK1,k10_yellow_6(sK0,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ~spl8_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f97])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ~r2_hidden(sK1,k2_pre_topc(sK0,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl8_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f92])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl8_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f87])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl8_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f82])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    l1_waybel_0(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl8_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f77])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl8_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f72])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~spl8_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f67])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f62])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v7_waybel_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f57])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v4_orders_2(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ~spl8_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f52])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ~v2_struct_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (24610)------------------------------
% 0.21/0.49  % (24610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24610)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (24610)Memory used [KB]: 6268
% 0.21/0.49  % (24610)Time elapsed: 0.076 s
% 0.21/0.49  % (24610)------------------------------
% 0.21/0.49  % (24610)------------------------------
% 0.21/0.49  % (24601)Success in time 0.134 s
%------------------------------------------------------------------------------
