%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1958+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 490 expanded)
%              Number of leaves         :   14 ( 111 expanded)
%              Depth                    :   21
%              Number of atoms          :  382 (2912 expanded)
%              Number of equality atoms :   51 ( 567 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f61,f246,f372])).

fof(f372,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f370,f37])).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
      | ~ v7_struct_0(sK0) )
    & ( k3_yellow_0(sK0) = k4_yellow_0(sK0)
      | v7_struct_0(sK0) )
    & l1_orders_2(sK0)
    & v3_yellow_0(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
          | ~ v7_struct_0(X0) )
        & ( k3_yellow_0(X0) = k4_yellow_0(X0)
          | v7_struct_0(X0) )
        & l1_orders_2(X0)
        & v3_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
        | ~ v7_struct_0(sK0) )
      & ( k3_yellow_0(sK0) = k4_yellow_0(sK0)
        | v7_struct_0(sK0) )
      & l1_orders_2(sK0)
      & v3_yellow_0(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
        | ~ v7_struct_0(X0) )
      & ( k3_yellow_0(X0) = k4_yellow_0(X0)
        | v7_struct_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
        | ~ v7_struct_0(X0) )
      & ( k3_yellow_0(X0) = k4_yellow_0(X0)
        | v7_struct_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( v7_struct_0(X0)
      <~> k3_yellow_0(X0) = k4_yellow_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( v7_struct_0(X0)
      <~> k3_yellow_0(X0) = k4_yellow_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_struct_0(X0)
        <=> k3_yellow_0(X0) = k4_yellow_0(X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> k3_yellow_0(X0) = k4_yellow_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_waybel_7)).

fof(f370,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f364,f59])).

fof(f59,plain,
    ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_2
  <=> k3_yellow_0(sK0) = k4_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f364,plain,
    ( k3_yellow_0(sK0) = k4_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f314,f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f314,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_yellow_0(sK0) = X0 )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f313,f111])).

fof(f111,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f313,plain,
    ( ! [X0] :
        ( k4_yellow_0(sK0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(sK0) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f301,f54])).

fof(f54,plain,
    ( v7_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_1
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f301,plain,(
    ! [X0] :
      ( k4_yellow_0(sK0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_struct_0(sK0)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f107,f43])).

fof(f43,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ( sK1(X0) != sK2(X0)
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f32,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK1(X0) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK1(X0) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK1(X0) != sK2(X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( X1 = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v7_struct_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_struct_0)).

fof(f107,plain,(
    m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f37,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_0)).

fof(f246,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f244,f111])).

fof(f244,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f243,f55])).

fof(f55,plain,
    ( ~ v7_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f243,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f235,f237])).

fof(f237,plain,
    ( k3_yellow_0(sK0) != sK2(sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f124,f230])).

fof(f230,plain,
    ( k3_yellow_0(sK0) = sK1(sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f155,f122])).

fof(f122,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f119,f111])).

fof(f119,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | spl3_1 ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f155,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_yellow_0(sK0) = X2 )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f154,f100])).

fof(f100,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f99,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f97])).

fof(f97,plain,(
    v1_yellow_0(sK0) ),
    inference(subsumption_resolution,[],[f89,f37])).

fof(f89,plain,
    ( v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_0)).

fof(f36,plain,(
    v3_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_yellow_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f37])).

fof(f85,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v1_yellow_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f35,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f154,plain,
    ( ! [X2] :
        ( k3_yellow_0(sK0) = X2
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f153,f105])).

fof(f105,plain,
    ( ! [X1] :
        ( r1_orders_2(sK0,X1,k3_yellow_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f104,f58])).

fof(f58,plain,
    ( k3_yellow_0(sK0) = k4_yellow_0(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f104,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,k4_yellow_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f103,f34])).

fof(f103,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,k4_yellow_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f102,f101])).

fof(f101,plain,(
    v2_yellow_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f37])).

fof(f90,plain,
    ( v2_yellow_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,k4_yellow_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_yellow_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f37])).

fof(f86,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,k4_yellow_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v2_yellow_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

fof(f153,plain,
    ( ! [X2] :
        ( k3_yellow_0(sK0) = X2
        | ~ r1_orders_2(sK0,X2,k3_yellow_0(sK0))
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f152,plain,
    ( ! [X2] :
        ( k3_yellow_0(sK0) = X2
        | ~ r1_orders_2(sK0,X2,k3_yellow_0(sK0))
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f141,f37])).

fof(f141,plain,
    ( ! [X2] :
        ( k3_yellow_0(sK0) = X2
        | ~ r1_orders_2(sK0,X2,k3_yellow_0(sK0))
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f114,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f114,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f107,f58])).

fof(f124,plain,
    ( sK1(sK0) != sK2(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f121,f111])).

fof(f121,plain,
    ( sK1(sK0) != sK2(sK0)
    | ~ l1_struct_0(sK0)
    | spl3_1 ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | sK1(X0) != sK2(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f235,plain,
    ( k3_yellow_0(sK0) = sK2(sK0)
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f155,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f38,f57,f53])).

fof(f38,plain,
    ( k3_yellow_0(sK0) = k4_yellow_0(sK0)
    | v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f57,f53])).

fof(f39,plain,
    ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
