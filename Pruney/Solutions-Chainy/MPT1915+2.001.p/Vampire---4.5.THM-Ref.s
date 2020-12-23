%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 129 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  286 ( 544 expanded)
%              Number of equality atoms :   66 ( 123 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f60,f72,f78,f88,f102,f134,f146])).

fof(f146,plain,
    ( ~ spl3_1
    | spl3_5
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl3_1
    | spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f144,f59])).

fof(f59,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_5
  <=> u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f144,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(resolution,[],[f133,f39])).

fof(f39,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(X0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_17
  <=> ! [X0] :
        ( u1_struct_0(X0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f134,plain,
    ( spl3_17
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f104,f100,f132])).

fof(f100,plain,
    ( spl3_10
  <=> ! [X11,X10] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X10,X11)
        | u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = X10
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f104,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0) )
    | ~ spl3_10 ),
    inference(resolution,[],[f101,f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f101,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10)))
        | u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = X10
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X10,X11) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f93,f85,f100])).

fof(f85,plain,
    ( spl3_8
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f93,plain,
    ( ! [X10,X11] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X10,X11)
        | u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = X10
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))) )
    | ~ spl3_8 ),
    inference(superposition,[],[f30,f87])).

fof(f87,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f88,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f83,f76,f37,f85])).

fof(f76,plain,
    ( spl3_7
  <=> ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,sK1,sK2)),u1_orders_2(k3_yellow_6(X0,sK1,sK2)))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f83,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f77,f39])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,sK1,sK2)),u1_orders_2(k3_yellow_6(X0,sK1,sK2))) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f73,f70,f52,f76])).

fof(f52,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0)))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f73,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,sK1,sK2)),u1_orders_2(k3_yellow_6(X0,sK1,sK2)))
        | ~ l1_orders_2(X0) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0)))
        | ~ l1_orders_2(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f72,plain,
    ( spl3_6
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f66,f47,f42,f70])).

fof(f42,plain,
    ( spl3_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,
    ( spl3_3
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0)))
        | ~ l1_orders_2(X1) )
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f65,f44])).

fof(f44,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0)))
        | v2_struct_0(sK1)
        | ~ l1_orders_2(X1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f63,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0) )
     => ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_6)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | ~ v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | ~ l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | k3_yellow_6(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X1)
      | ~ v6_waybel_0(X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X1)
                    & v6_waybel_0(X3,X1) )
                 => ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_6)).

fof(f60,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,X1,X2))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_6)).

fof(f55,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (22926)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (22926)Refutation not found, incomplete strategy% (22926)------------------------------
% 0.21/0.49  % (22926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22926)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (22926)Memory used [KB]: 6012
% 0.21/0.49  % (22926)Time elapsed: 0.091 s
% 0.21/0.49  % (22926)------------------------------
% 0.21/0.49  % (22926)------------------------------
% 0.21/0.49  % (22915)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (22914)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22913)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (22921)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (22913)Refutation not found, incomplete strategy% (22913)------------------------------
% 0.21/0.50  % (22913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22913)Memory used [KB]: 10490
% 0.21/0.50  % (22913)Time elapsed: 0.085 s
% 0.21/0.50  % (22913)------------------------------
% 0.21/0.50  % (22913)------------------------------
% 0.21/0.50  % (22915)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f60,f72,f78,f88,f102,f134,f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ~spl3_1 | spl3_5 | ~spl3_17),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_5 | ~spl3_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f144,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) | spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl3_5 <=> u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) | (~spl3_1 | ~spl3_17)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) | (~spl3_1 | ~spl3_17)),
% 0.21/0.50    inference(resolution,[],[f133,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    spl3_1 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(X0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2))) ) | ~spl3_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl3_17 <=> ! [X0] : (u1_struct_0(X0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | ~l1_orders_2(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl3_17 | ~spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f100,f132])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl3_10 <=> ! [X11,X10] : (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X10,X11) | u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = X10 | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X0] : (u1_struct_0(X0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | ~l1_orders_2(X0)) ) | ~spl3_10),
% 0.21/0.50    inference(resolution,[],[f101,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X10,X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))) | u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = X10 | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X10,X11)) ) | ~spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl3_10 | ~spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f93,f85,f100])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl3_8 <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X10,X11] : (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X10,X11) | u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = X10 | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10)))) ) | ~spl3_8),
% 0.21/0.50    inference(superposition,[],[f30,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2))) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl3_8 | ~spl3_1 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f83,f76,f37,f85])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl3_7 <=> ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,sK1,sK2)),u1_orders_2(k3_yellow_6(X0,sK1,sK2))) | ~l1_orders_2(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2))) | (~spl3_1 | ~spl3_7)),
% 0.21/0.50    inference(resolution,[],[f77,f39])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,sK1,sK2)),u1_orders_2(k3_yellow_6(X0,sK1,sK2)))) ) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl3_7 | ~spl3_4 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f70,f52,f76])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl3_4 <=> m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl3_6 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0))) | ~l1_orders_2(X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,sK1,sK2)),u1_orders_2(k3_yellow_6(X0,sK1,sK2))) | ~l1_orders_2(X0)) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.50    inference(resolution,[],[f71,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f52])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0))) | ~l1_orders_2(X1)) ) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl3_6 | spl3_2 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f66,f47,f42,f70])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl3_2 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl3_3 <=> l1_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0))) | ~l1_orders_2(X1)) ) | (spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f65,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v2_struct_0(sK1) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0))) | v2_struct_0(sK1) | ~l1_orders_2(X1)) ) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f64,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    l1_struct_0(sK1) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f47])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2))) | v2_struct_0(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow_6(X0,X1,X2),X1) & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow_6(X0,X1,X2),X1) & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_struct_0(X1) & ~v2_struct_0(X1) & l1_orders_2(X0)) => (l1_waybel_0(k3_yellow_6(X0,X1,X2),X1) & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_6)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2))) | ~v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f35,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow_6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2))) | ~l1_waybel_0(k3_yellow_6(X0,X1,X2),X1) | ~v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) | k3_yellow_6(X0,X1,X2) != X3 | ~l1_waybel_0(X3,X1) | ~v6_waybel_0(X3,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_yellow_6(X0,X1,X2) = X3 | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2)) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2)) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | k3_yellow_6(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X1) | ~v6_waybel_0(X3,X1)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_yellow_6(X0,X1,X2) = X3 | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2)) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2)) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | k3_yellow_6(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X1) | ~v6_waybel_0(X3,X1)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k3_yellow_6(X0,X1,X2) = X3 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2)) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) | ~l1_waybel_0(X3,X1) | ~v6_waybel_0(X3,X1)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k3_yellow_6(X0,X1,X2) = X3 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2)) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) | (~l1_waybel_0(X3,X1) | ~v6_waybel_0(X3,X1))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X1) & v6_waybel_0(X3,X1)) => (k3_yellow_6(X0,X1,X2) = X3 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2)) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_6)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f57])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ((u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_orders_2(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X2] : (u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK1))) => (u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_orders_2(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_6)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f52])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f47])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    l1_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f42])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f37])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (22915)------------------------------
% 0.21/0.50  % (22915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22915)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (22915)Memory used [KB]: 6268
% 0.21/0.50  % (22915)Time elapsed: 0.088 s
% 0.21/0.50  % (22915)------------------------------
% 0.21/0.50  % (22915)------------------------------
% 0.21/0.50  % (22918)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (22912)Success in time 0.139 s
%------------------------------------------------------------------------------
