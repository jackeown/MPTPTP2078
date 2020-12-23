%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2067+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  257 ( 842 expanded)
%              Number of leaves         :   51 ( 390 expanded)
%              Depth                    :   17
%              Number of atoms          : 1715 (6431 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f652,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f133,f138,f143,f148,f159,f164,f170,f177,f182,f187,f192,f197,f207,f240,f263,f272,f297,f315,f358,f363,f368,f382,f419,f424,f440,f445,f459,f468,f509,f519,f627,f651])).

fof(f651,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_21
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_21
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f649,f630])).

fof(f630,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f153,f147,f296,f314,f508,f452,f626,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X3)
      | ~ r3_waybel_9(X0,X3,X2)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK4(X0,X1,X2),X1)
                    & l1_waybel_0(sK4(X0,X1,X2),X0)
                    & v7_waybel_0(sK4(X0,X1,X2))
                    & v4_orders_2(sK4(X0,X1,X2))
                    & ~ v2_struct_0(sK4(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK4(X0,X1,X2),X1)
        & l1_waybel_0(sK4(X0,X1,X2),X0)
        & v7_waybel_0(sK4(X0,X1,X2))
        & v4_orders_2(sK4(X0,X1,X2))
        & ~ v2_struct_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r3_waybel_9(X0,X4,X2)
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r3_waybel_9(X0,X3,X2)
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).

fof(f626,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK1)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f624])).

fof(f624,plain,
    ( spl6_39
  <=> r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f452,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl6_33
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f508,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl6_36
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f314,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl6_23
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f296,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl6_22
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f147,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f153,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_6
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f142,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f137,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f127,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f649,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_21
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f646,f142])).

fof(f646,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_21
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(resolution,[],[f622,f169])).

fof(f169,plain,
    ( r1_waybel_7(sK0,sK3,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_9
  <=> r1_waybel_7(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f622,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f621,f271])).

fof(f271,plain,
    ( sK3 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl6_21
  <=> sK3 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f621,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f620,f127])).

fof(f620,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f619,f137])).

fof(f619,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ l1_pre_topc(sK0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | spl6_22
    | ~ spl6_23
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f618,f452])).

fof(f618,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ l1_pre_topc(sK0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | spl6_22
    | ~ spl6_23
    | ~ spl6_36 ),
    inference(resolution,[],[f516,f132])).

fof(f516,plain,
    ( ! [X4,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X3)
        | r3_waybel_9(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X4)
        | ~ l1_pre_topc(X3)
        | ~ r1_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X4)
        | v2_struct_0(X3) )
    | spl6_22
    | ~ spl6_23
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f515,f296])).

fof(f515,plain,
    ( ! [X4,X3] :
        ( ~ r1_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X3)
        | r3_waybel_9(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X4)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl6_23
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f511,f314])).

fof(f511,plain,
    ( ! [X4,X3] :
        ( ~ r1_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),X4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),X3)
        | r3_waybel_9(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X4)
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl6_36 ),
    inference(resolution,[],[f508,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r3_waybel_9(X0,X1,X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

fof(f627,plain,
    ( spl6_39
    | spl6_1
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_21
    | spl6_22
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f599,f451,f294,f269,f184,f161,f125,f624])).

fof(f161,plain,
    ( spl6_8
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f184,plain,
    ( spl6_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f599,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK1)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_21
    | spl6_22
    | ~ spl6_33 ),
    inference(unit_resulting_resolution,[],[f163,f566])).

fof(f566,plain,
    ( ! [X5] :
        ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X5)
        | ~ r2_hidden(X5,sK3) )
    | spl6_1
    | ~ spl6_12
    | ~ spl6_21
    | spl6_22
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f565,f271])).

fof(f565,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)))
        | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X5) )
    | spl6_1
    | ~ spl6_12
    | spl6_22
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f564,f127])).

fof(f564,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)))
        | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X5)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | spl6_22
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f563,f186])).

fof(f186,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f184])).

fof(f563,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)))
        | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X5)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | spl6_22
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f533,f296])).

fof(f533,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)))
        | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X5)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_33 ),
    inference(resolution,[],[f452,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

fof(f163,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f161])).

fof(f519,plain,
    ( spl6_33
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_15
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f480,f260,f204,f194,f184,f179,f174,f156,f125,f451])).

fof(f156,plain,
    ( spl6_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f174,plain,
    ( spl6_10
  <=> v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f179,plain,
    ( spl6_11
  <=> v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f194,plain,
    ( spl6_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f204,plain,
    ( spl6_15
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f260,plain,
    ( spl6_20
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f480,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_15
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f324,f196])).

fof(f196,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f194])).

fof(f324,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_15
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f323,f206])).

fof(f206,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f204])).

fof(f323,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f322,f262])).

fof(f262,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f260])).

fof(f322,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f321,f158])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f156])).

fof(f321,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | spl6_1
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f289,f176])).

fof(f176,plain,
    ( v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f289,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | spl6_1
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(resolution,[],[f226,f181])).

fof(f181,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f179])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        | ~ v2_waybel_0(X0,k3_yellow_1(X1))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) )
    | spl6_1
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f225,f127])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        | ~ v13_waybel_0(X0,k3_yellow_1(X1))
        | ~ v2_waybel_0(X0,k3_yellow_1(X1))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f116,f186])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f509,plain,
    ( spl6_36
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f479,f260,f204,f194,f189,f184,f179,f174,f156,f125,f506])).

fof(f189,plain,
    ( spl6_13
  <=> v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f479,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f320,f196])).

fof(f320,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_15
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f319,f206])).

fof(f319,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f318,f262])).

fof(f318,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f317,f158])).

fof(f317,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f316,f176])).

fof(f316,plain,
    ( ~ v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f300,f181])).

fof(f300,plain,
    ( ~ v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(resolution,[],[f228,f191])).

fof(f191,plain,
    ( v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f189])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
        | ~ v13_waybel_0(X0,k3_yellow_1(X1))
        | ~ v2_waybel_0(X0,k3_yellow_1(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v7_waybel_0(k3_yellow19(sK0,X1,X0)) )
    | spl6_1
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f227,f127])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        | ~ v13_waybel_0(X0,k3_yellow_1(X1))
        | ~ v2_waybel_0(X0,k3_yellow_1(X1))
        | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v7_waybel_0(k3_yellow19(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f118,f186])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f468,plain,
    ( spl6_1
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27
    | spl6_31
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | spl6_1
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27
    | spl6_31
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f466,f444])).

fof(f444,plain,
    ( r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl6_32
  <=> r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f466,plain,
    ( ~ r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | spl6_1
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27
    | spl6_31
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f465,f387])).

fof(f387,plain,
    ( m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl6_1
    | ~ spl6_12
    | spl6_26
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f127,f186,f367,f381,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow19)).

fof(f381,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl6_27
  <=> l1_waybel_0(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f367,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1,sK2))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl6_26
  <=> v2_struct_0(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f465,plain,
    ( ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | spl6_1
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27
    | spl6_31
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f464,f389])).

fof(f389,plain,
    ( v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | spl6_1
    | ~ spl6_12
    | spl6_26
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f127,f186,f367,f381,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow19)).

fof(f464,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | spl6_1
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27
    | spl6_31
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f463,f386])).

fof(f386,plain,
    ( v2_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | spl6_1
    | ~ spl6_12
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f127,f186,f367,f362,f357,f381,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (27073)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow19)).

fof(f357,plain,
    ( v7_waybel_0(sK4(sK0,sK1,sK2))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl6_24
  <=> v7_waybel_0(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f362,plain,
    ( v4_orders_2(sK4(sK0,sK1,sK2))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl6_25
  <=> v4_orders_2(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f463,plain,
    ( ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | spl6_1
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27
    | spl6_31
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f462,f385])).

fof(f385,plain,
    ( v1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | spl6_1
    | ~ spl6_12
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f127,f186,f367,f362,f357,f381,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f462,plain,
    ( ~ v1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl6_17
    | spl6_31
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f461,f439])).

fof(f439,plain,
    ( ~ v1_xboole_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl6_31
  <=> v1_xboole_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f461,plain,
    ( v1_xboole_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ v1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl6_17
    | ~ spl6_34 ),
    inference(resolution,[],[f458,f239])).

fof(f239,plain,
    ( ! [X3] :
        ( ~ r1_waybel_7(sK0,X3,sK2)
        | v1_xboole_0(X3)
        | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X3) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl6_17
  <=> ! [X3] :
        ( ~ r1_waybel_7(sK0,X3,sK2)
        | v1_xboole_0(X3)
        | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f458,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,sK4(sK0,sK1,sK2)),sK2)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl6_34
  <=> r1_waybel_7(sK0,k2_yellow19(sK0,sK4(sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f459,plain,
    ( spl6_34
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f430,f416,f379,f365,f360,f355,f140,f135,f130,f125,f456])).

fof(f416,plain,
    ( spl6_28
  <=> r3_waybel_9(sK0,sK4(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f430,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,sK4(sK0,sK1,sK2)),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_25
    | spl6_26
    | ~ spl6_27
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f367,f362,f357,f381,f418,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f418,plain,
    ( r3_waybel_9(sK0,sK4(sK0,sK1,sK2),sK2)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f416])).

fof(f445,plain,
    ( spl6_32
    | spl6_1
    | ~ spl6_5
    | ~ spl6_12
    | spl6_26
    | ~ spl6_27
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f433,f421,f379,f365,f184,f145,f125,f442])).

fof(f421,plain,
    ( spl6_29
  <=> r1_waybel_0(sK0,sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f433,plain,
    ( r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | spl6_1
    | ~ spl6_5
    | ~ spl6_12
    | spl6_26
    | ~ spl6_27
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f127,f186,f367,f147,f381,f423,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,X2)
      | r2_hidden(X2,k2_yellow19(X0,X1))
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f423,plain,
    ( r1_waybel_0(sK0,sK4(sK0,sK1,sK2),sK1)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f421])).

fof(f440,plain,
    ( ~ spl6_31
    | spl6_1
    | ~ spl6_12
    | spl6_26
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f388,f379,f365,f184,f125,f437])).

fof(f388,plain,
    ( ~ v1_xboole_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | spl6_1
    | ~ spl6_12
    | spl6_26
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f127,f186,f367,f381,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f424,plain,
    ( spl6_29
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f341,f152,f145,f140,f135,f130,f125,f421])).

fof(f341,plain,
    ( r1_waybel_0(sK0,sK4(sK0,sK1,sK2),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f147,f154,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f154,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f419,plain,
    ( spl6_28
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f340,f152,f145,f140,f135,f130,f125,f416])).

fof(f340,plain,
    ( r3_waybel_9(sK0,sK4(sK0,sK1,sK2),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f147,f154,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f382,plain,
    ( spl6_27
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f342,f152,f145,f140,f135,f130,f125,f379])).

fof(f342,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f147,f154,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | l1_waybel_0(sK4(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f368,plain,
    ( ~ spl6_26
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f345,f152,f145,f140,f135,f130,f125,f365])).

fof(f345,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f147,f154,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f363,plain,
    ( spl6_25
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f344,f152,f145,f140,f135,f130,f125,f360])).

fof(f344,plain,
    ( v4_orders_2(sK4(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f147,f154,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_orders_2(sK4(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f358,plain,
    ( spl6_24
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f343,f152,f145,f140,f135,f130,f125,f355])).

fof(f343,plain,
    ( v7_waybel_0(sK4(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f147,f154,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v7_waybel_0(sK4(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f315,plain,
    ( spl6_23
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_15
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f265,f260,f204,f194,f184,f179,f174,f156,f125,f312])).

fof(f265,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_15
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f127,f158,f186,f206,f181,f176,f196,f262,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f297,plain,
    ( ~ spl6_22
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_15
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f264,f260,f204,f194,f184,f179,f174,f156,f125,f294])).

fof(f264,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_15
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f127,f186,f158,f206,f181,f176,f196,f262,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f272,plain,
    ( spl6_21
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f246,f194,f189,f184,f179,f174,f156,f125,f269])).

fof(f246,plain,
    ( sK3 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl6_1
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f127,f186,f158,f181,f176,f191,f196,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f263,plain,
    ( spl6_20
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f199,f184,f260])).

fof(f199,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f186,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f240,plain,
    ( ~ spl6_6
    | spl6_17 ),
    inference(avatar_split_clause,[],[f88,f238,f152])).

fof(f88,plain,(
    ! [X3] :
      ( ~ r1_waybel_7(sK0,X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(X3)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f64])).

% (27077)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f64,plain,
    ( ( ! [X3] :
          ( ~ r1_waybel_7(sK0,X3,sK2)
          | ~ r2_hidden(sK1,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          | v1_xboole_0(X3) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ( r1_waybel_7(sK0,sK3,sK2)
        & r2_hidden(sK1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(sK3) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f63,f62,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ? [X4] :
                      ( r1_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X4) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(sK0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(sK0,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r1_waybel_7(sK0,X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                  | v1_xboole_0(X3) )
              | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & ( ? [X4] :
                  ( r1_waybel_7(sK0,X4,X2)
                  & r2_hidden(X1,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                  & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                  & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                  & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                  & ~ v1_xboole_0(X4) )
              | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r1_waybel_7(sK0,X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                | v1_xboole_0(X3) )
            | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & ( ? [X4] :
                ( r1_waybel_7(sK0,X4,X2)
                & r2_hidden(sK1,X4)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                & ~ v1_xboole_0(X4) )
            | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r1_waybel_7(sK0,X3,X2)
              | ~ r2_hidden(sK1,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
              | v1_xboole_0(X3) )
          | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & ( ? [X4] :
              ( r1_waybel_7(sK0,X4,X2)
              & r2_hidden(sK1,X4)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
              & ~ v1_xboole_0(X4) )
          | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ! [X3] :
            ( ~ r1_waybel_7(sK0,X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
            | v1_xboole_0(X3) )
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & ( ? [X4] :
            ( r1_waybel_7(sK0,X4,sK2)
            & r2_hidden(sK1,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
            & ~ v1_xboole_0(X4) )
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X4] :
        ( r1_waybel_7(sK0,X4,sK2)
        & r2_hidden(sK1,X4)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X4) )
   => ( r1_waybel_7(sK0,sK3,sK2)
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(X0,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ? [X3] :
                      ( r1_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).

fof(f207,plain,
    ( ~ spl6_15
    | spl6_1
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f200,f184,f125,f204])).

fof(f200,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl6_1
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f127,f186,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f197,plain,
    ( spl6_6
    | spl6_14 ),
    inference(avatar_split_clause,[],[f85,f194,f152])).

fof(f85,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f192,plain,
    ( spl6_6
    | spl6_13 ),
    inference(avatar_split_clause,[],[f82,f189,f152])).

fof(f82,plain,
    ( v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f187,plain,
    ( spl6_12
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f149,f135,f184])).

fof(f149,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f137,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f182,plain,
    ( spl6_6
    | spl6_11 ),
    inference(avatar_split_clause,[],[f84,f179,f152])).

fof(f84,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f177,plain,
    ( spl6_6
    | spl6_10 ),
    inference(avatar_split_clause,[],[f83,f174,f152])).

fof(f83,plain,
    ( v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f170,plain,
    ( spl6_6
    | spl6_9 ),
    inference(avatar_split_clause,[],[f87,f167,f152])).

fof(f87,plain,
    ( r1_waybel_7(sK0,sK3,sK2)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f164,plain,
    ( spl6_6
    | spl6_8 ),
    inference(avatar_split_clause,[],[f86,f161,f152])).

fof(f86,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f159,plain,
    ( spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f81,f156,f152])).

fof(f81,plain,
    ( ~ v1_xboole_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f148,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f79,f145])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f143,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f80,f140])).

fof(f80,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f64])).

fof(f138,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f78,f135])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f133,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f77,f130])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f128,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f76,f125])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f64])).

%------------------------------------------------------------------------------
