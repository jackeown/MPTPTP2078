%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 330 expanded)
%              Number of leaves         :   10 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          :  392 (2750 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f73,f76,f85])).

fof(f85,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f83,f24])).

fof(f24,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_waybel_0(sK0,sK3,sK1)
    & m2_yellow_6(sK3,sK0,sK2)
    & r1_waybel_0(sK0,sK2,sK1)
    & l1_waybel_0(sK2,sK0)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ~ r1_waybel_0(X0,X3,X1)
                & m2_yellow_6(X3,X0,X2) )
            & r1_waybel_0(X0,X2,X1)
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ~ r1_waybel_0(sK0,X3,X1)
              & m2_yellow_6(X3,sK0,X2) )
          & r1_waybel_0(sK0,X2,X1)
          & l1_waybel_0(X2,sK0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2,X1] :
        ( ? [X3] :
            ( ~ r1_waybel_0(sK0,X3,X1)
            & m2_yellow_6(X3,sK0,X2) )
        & r1_waybel_0(sK0,X2,X1)
        & l1_waybel_0(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_waybel_0(sK0,X3,sK1)
          & m2_yellow_6(X3,sK0,sK2) )
      & r1_waybel_0(sK0,sK2,sK1)
      & l1_waybel_0(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r1_waybel_0(sK0,X3,sK1)
        & m2_yellow_6(X3,sK0,sK2) )
   => ( ~ r1_waybel_0(sK0,sK3,sK1)
      & m2_yellow_6(sK3,sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_waybel_0(X0,X3,X1)
              & m2_yellow_6(X3,X0,X2) )
          & r1_waybel_0(X0,X2,X1)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_waybel_0(X0,X3,X1)
              & m2_yellow_6(X3,X0,X2) )
          & r1_waybel_0(X0,X2,X1)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
           => ( r1_waybel_0(X0,X2,X1)
             => ! [X3] :
                  ( m2_yellow_6(X3,X0,X2)
                 => r1_waybel_0(X0,X3,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
         => ( r1_waybel_0(X0,X2,X1)
           => ! [X3] :
                ( m2_yellow_6(X3,X0,X2)
               => r1_waybel_0(X0,X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow19)).

fof(f83,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f82,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,
    ( v2_struct_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f81,f22])).

fof(f22,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,
    ( ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f80,f23])).

fof(f23,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,
    ( ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f79,f26])).

fof(f26,plain,(
    m2_yellow_6(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(sK3,sK0,X0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f78,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m2_yellow_6(sK3,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f77,f20])).

fof(f20,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ m2_yellow_6(sK3,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f60,plain,
    ( v2_struct_0(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f76,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f74,f25])).

fof(f25,plain,(
    r1_waybel_0(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,
    ( ~ r1_waybel_0(sK0,sK2,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f66,f27])).

fof(f27,plain,(
    ~ r1_waybel_0(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK3,X0)
        | ~ r1_waybel_0(sK0,sK2,X0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_3
  <=> ! [X0] :
        ( ~ r1_waybel_0(sK0,sK2,X0)
        | r1_waybel_0(sK0,sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f71,f22])).

fof(f71,plain,
    ( ~ v4_orders_2(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f70,f21])).

fof(f70,plain,
    ( v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f69,f23])).

fof(f69,plain,
    ( ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f68,f24])).

fof(f68,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f63,f26])).

fof(f63,plain,
    ( ! [X1] :
        ( ~ m2_yellow_6(sK3,sK0,X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v7_waybel_0(X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_2
  <=> ! [X1] :
        ( ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ m2_yellow_6(sK3,sK0,X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f67,plain,
    ( spl4_1
    | spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f56,f65,f62,f58])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_0(sK0,sK2,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m2_yellow_6(sK3,sK0,X1)
      | ~ l1_waybel_0(X1,sK0)
      | v2_struct_0(sK3)
      | r1_waybel_0(sK0,sK3,X0) ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(sK0,X1,k6_subset_1(u1_struct_0(sK0),X2))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_yellow_6(X1,sK0,X0)
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X1)
      | r1_waybel_0(sK0,X1,X2) ) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f35,f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f30,f20])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m2_yellow_6(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f39,f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m2_yellow_6(X0,sK0,X1)
      | ~ l1_waybel_0(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | l1_waybel_0(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f34,f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | l1_waybel_0(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f54,f19])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_waybel_0(sK0,sK2,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f53,f20])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_waybel_0(sK0,sK2,X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f52,f21])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_waybel_0(sK0,sK2,X0)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f51,f24])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_waybel_0(sK0,sK2,X0)
      | ~ l1_waybel_0(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0] :
      ( r2_waybel_0(sK0,sK2,X0)
      | ~ r2_waybel_0(sK0,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f49,f21])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,X0)
      | v2_struct_0(sK2)
      | r2_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f48,f22])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,X0)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | r2_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f47,f23])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,X0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | r2_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f46,f24])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK3,X0)
      | ~ l1_waybel_0(sK2,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | r2_waybel_0(sK0,sK2,X0) ) ),
    inference(resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X0,sK0,X2)
      | ~ r2_waybel_0(sK0,X0,X1)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | r2_waybel_0(sK0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f44,f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(sK0,X0,X1)
      | ~ m2_yellow_6(X0,sK0,X2)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | r2_waybel_0(sK0,X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f28,f20])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (32716)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.48  % (32731)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  % (32716)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f67,f73,f76,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ~spl4_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    $false | ~spl4_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f83,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    l1_waybel_0(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ((~r1_waybel_0(sK0,sK3,sK1) & m2_yellow_6(sK3,sK0,sK2)) & r1_waybel_0(sK0,sK2,sK1) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0] : (? [X1,X2] : (? [X3] : (~r1_waybel_0(X0,X3,X1) & m2_yellow_6(X3,X0,X2)) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : (? [X3] : (~r1_waybel_0(sK0,X3,X1) & m2_yellow_6(X3,sK0,X2)) & r1_waybel_0(sK0,X2,X1) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X2,X1] : (? [X3] : (~r1_waybel_0(sK0,X3,X1) & m2_yellow_6(X3,sK0,X2)) & r1_waybel_0(sK0,X2,X1) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r1_waybel_0(sK0,X3,sK1) & m2_yellow_6(X3,sK0,sK2)) & r1_waybel_0(sK0,sK2,sK1) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X3] : (~r1_waybel_0(sK0,X3,sK1) & m2_yellow_6(X3,sK0,sK2)) => (~r1_waybel_0(sK0,sK3,sK1) & m2_yellow_6(sK3,sK0,sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1,X2] : (? [X3] : (~r1_waybel_0(X0,X3,X1) & m2_yellow_6(X3,X0,X2)) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0] : (? [X1,X2] : ((? [X3] : (~r1_waybel_0(X0,X3,X1) & m2_yellow_6(X3,X0,X2)) & r1_waybel_0(X0,X2,X1)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m2_yellow_6(X3,X0,X2) => r1_waybel_0(X0,X3,X1)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m2_yellow_6(X3,X0,X2) => r1_waybel_0(X0,X3,X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow19)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ~l1_waybel_0(sK2,sK0) | ~spl4_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f82,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ~v2_struct_0(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    v2_struct_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~spl4_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    v4_orders_2(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~spl4_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f80,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    v7_waybel_0(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~spl4_1),
% 0.22/0.48    inference(resolution,[],[f79,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    m2_yellow_6(sK3,sK0,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X0] : (~m2_yellow_6(sK3,sK0,X0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0)) ) | ~spl4_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f78,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m2_yellow_6(sK3,sK0,X0) | v2_struct_0(sK0)) ) | ~spl4_1),
% 0.22/0.48    inference(resolution,[],[f77,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    l1_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~m2_yellow_6(sK3,X0,X1) | v2_struct_0(X0)) ) | ~spl4_1),
% 0.22/0.48    inference(resolution,[],[f60,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    v2_struct_0(sK3) | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl4_1 <=> v2_struct_0(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ~spl4_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    $false | ~spl4_3),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    r1_waybel_0(sK0,sK2,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ~r1_waybel_0(sK0,sK2,sK1) | ~spl4_3),
% 0.22/0.48    inference(resolution,[],[f66,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ~r1_waybel_0(sK0,sK3,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0] : (r1_waybel_0(sK0,sK3,X0) | ~r1_waybel_0(sK0,sK2,X0)) ) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl4_3 <=> ! [X0] : (~r1_waybel_0(sK0,sK2,X0) | r1_waybel_0(sK0,sK3,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ~spl4_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    $false | ~spl4_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f71,f22])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ~v4_orders_2(sK2) | ~spl4_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f70,f21])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~spl4_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f69,f23])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~v7_waybel_0(sK2) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~spl4_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f24])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~spl4_2),
% 0.22/0.48    inference(resolution,[],[f63,f26])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X1] : (~m2_yellow_6(sK3,sK0,X1) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | v2_struct_0(X1) | ~v4_orders_2(X1)) ) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl4_2 <=> ! [X1] : (~v7_waybel_0(X1) | ~l1_waybel_0(X1,sK0) | ~m2_yellow_6(sK3,sK0,X1) | v2_struct_0(X1) | ~v4_orders_2(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl4_1 | spl4_2 | spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f56,f65,f62,f58])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK0,sK2,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~m2_yellow_6(sK3,sK0,X1) | ~l1_waybel_0(X1,sK0) | v2_struct_0(sK3) | r1_waybel_0(sK0,sK3,X0)) )),
% 0.22/0.48    inference(resolution,[],[f55,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_waybel_0(sK0,X1,k6_subset_1(u1_struct_0(sK0),X2)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m2_yellow_6(X1,sK0,X0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X1) | r1_waybel_0(sK0,X1,X2)) )),
% 0.22/0.48    inference(resolution,[],[f40,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f35,f19])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f30,f20])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r1_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (l1_waybel_0(X0,sK0) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~m2_yellow_6(X0,sK0,X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f39,f19])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m2_yellow_6(X0,sK0,X1) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | l1_waybel_0(X0,sK0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f34,f20])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | l1_waybel_0(X2,X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0)) | ~r1_waybel_0(sK0,sK2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f54,f19])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0)) | ~r1_waybel_0(sK0,sK2,X0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f53,f20])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0)) | ~r1_waybel_0(sK0,sK2,X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f52,f21])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0)) | ~r1_waybel_0(sK0,sK2,X0) | v2_struct_0(sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f51,f24])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,k6_subset_1(u1_struct_0(sK0),X0)) | ~r1_waybel_0(sK0,sK2,X0) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f50,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0] : (r2_waybel_0(sK0,sK2,X0) | ~r2_waybel_0(sK0,sK3,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f49,f21])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,X0) | v2_struct_0(sK2) | r2_waybel_0(sK0,sK2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f48,f22])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,X0) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | r2_waybel_0(sK0,sK2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f47,f23])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,X0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | r2_waybel_0(sK0,sK2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f46,f24])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK3,X0) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | r2_waybel_0(sK0,sK2,X0)) )),
% 0.22/0.48    inference(resolution,[],[f45,f26])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m2_yellow_6(X0,sK0,X2) | ~r2_waybel_0(sK0,X0,X1) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | r2_waybel_0(sK0,X2,X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f44,f19])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_waybel_0(sK0,X0,X1) | ~m2_yellow_6(X0,sK0,X2) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | r2_waybel_0(sK0,X2,X1) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f28,f20])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X3) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (32716)------------------------------
% 0.22/0.48  % (32716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (32716)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (32716)Memory used [KB]: 5373
% 0.22/0.48  % (32716)Time elapsed: 0.064 s
% 0.22/0.48  % (32716)------------------------------
% 0.22/0.48  % (32716)------------------------------
% 0.22/0.48  % (32715)Success in time 0.117 s
%------------------------------------------------------------------------------
