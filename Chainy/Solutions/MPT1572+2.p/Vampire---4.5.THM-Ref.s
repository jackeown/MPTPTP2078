%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1572+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:25 EST 2020

% Result     : Theorem 16.39s
% Output     : Refutation 16.39s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 835 expanded)
%              Number of leaves         :   19 ( 285 expanded)
%              Depth                    :   16
%              Number of atoms          :  827 (6837 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3842,f3843,f3844,f3845,f14675,f14679,f14721,f15796,f16098,f17051,f17863,f17874,f17918,f17919,f20102,f20189])).

fof(f20189,plain,
    ( spl50_1
    | ~ spl50_2
    | spl50_296
    | ~ spl50_297 ),
    inference(avatar_contradiction_clause,[],[f20188])).

fof(f20188,plain,
    ( $false
    | spl50_1
    | ~ spl50_2
    | spl50_296
    | ~ spl50_297 ),
    inference(subsumption_resolution,[],[f20187,f3386])).

fof(f3386,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3254])).

fof(f3254,plain,
    ( ( ( ~ r2_yellow_0(sK4,sK5)
        & r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4))) )
      | ( ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
        & r2_yellow_0(sK4,sK5) )
      | ( ~ r1_yellow_0(sK4,sK5)
        & r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4))) )
      | ( ~ r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
        & r1_yellow_0(sK4,sK5) ) )
    & l1_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f3056,f3253,f3252])).

fof(f3252,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_yellow_0(X0,X1)
              & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              & r2_yellow_0(X0,X1) )
            | ( ~ r1_yellow_0(X0,X1)
              & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              & r1_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r2_yellow_0(sK4,X1)
            & r2_yellow_0(sK4,k3_xboole_0(X1,u1_struct_0(sK4))) )
          | ( ~ r2_yellow_0(sK4,k3_xboole_0(X1,u1_struct_0(sK4)))
            & r2_yellow_0(sK4,X1) )
          | ( ~ r1_yellow_0(sK4,X1)
            & r1_yellow_0(sK4,k3_xboole_0(X1,u1_struct_0(sK4))) )
          | ( ~ r1_yellow_0(sK4,k3_xboole_0(X1,u1_struct_0(sK4)))
            & r1_yellow_0(sK4,X1) ) )
      & l1_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3253,plain,
    ( ? [X1] :
        ( ( ~ r2_yellow_0(sK4,X1)
          & r2_yellow_0(sK4,k3_xboole_0(X1,u1_struct_0(sK4))) )
        | ( ~ r2_yellow_0(sK4,k3_xboole_0(X1,u1_struct_0(sK4)))
          & r2_yellow_0(sK4,X1) )
        | ( ~ r1_yellow_0(sK4,X1)
          & r1_yellow_0(sK4,k3_xboole_0(X1,u1_struct_0(sK4))) )
        | ( ~ r1_yellow_0(sK4,k3_xboole_0(X1,u1_struct_0(sK4)))
          & r1_yellow_0(sK4,X1) ) )
   => ( ( ~ r2_yellow_0(sK4,sK5)
        & r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4))) )
      | ( ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
        & r2_yellow_0(sK4,sK5) )
      | ( ~ r1_yellow_0(sK4,sK5)
        & r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4))) )
      | ( ~ r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
        & r1_yellow_0(sK4,sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f3056,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3055])).

fof(f3055,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3033])).

fof(f3033,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
             => r2_yellow_0(X0,X1) )
            & ( r2_yellow_0(X0,X1)
             => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
             => r1_yellow_0(X0,X1) )
            & ( r1_yellow_0(X0,X1)
             => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f3032])).

fof(f3032,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X1)
           => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
           => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_yellow_0)).

fof(f20187,plain,
    ( v2_struct_0(sK4)
    | spl50_1
    | ~ spl50_2
    | spl50_296
    | ~ spl50_297 ),
    inference(subsumption_resolution,[],[f20186,f3387])).

fof(f3387,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f3254])).

fof(f20186,plain,
    ( ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl50_1
    | ~ spl50_2
    | spl50_296
    | ~ spl50_297 ),
    inference(subsumption_resolution,[],[f20185,f17894])).

fof(f17894,plain,
    ( m1_subset_1(sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
    | spl50_1
    | ~ spl50_2 ),
    inference(resolution,[],[f3829,f14680])).

fof(f14680,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK4,X0)
        | m1_subset_1(sK13(sK4,sK5,X0),u1_struct_0(sK4)) )
    | ~ spl50_2 ),
    inference(resolution,[],[f3832,f3859])).

fof(f3859,plain,(
    ! [X6,X7] :
      ( ~ r1_yellow_0(sK4,X7)
      | r1_yellow_0(sK4,X6)
      | m1_subset_1(sK13(sK4,X7,X6),u1_struct_0(sK4)) ) ),
    inference(subsumption_resolution,[],[f3849,f3387])).

fof(f3849,plain,(
    ! [X6,X7] :
      ( r1_yellow_0(sK4,X6)
      | ~ r1_yellow_0(sK4,X7)
      | m1_subset_1(sK13(sK4,X7,X6),u1_struct_0(sK4))
      | ~ l1_orders_2(sK4) ) ),
    inference(resolution,[],[f3386,f3474])).

fof(f3474,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3277,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK13(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK13(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK13(X0,X1,X2))
              | r2_lattice3(X0,X1,sK13(X0,X1,X2)) )
            & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f3275,f3276])).

fof(f3276,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK13(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK13(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK13(X0,X1,X2))
          | r2_lattice3(X0,X1,sK13(X0,X1,X2)) )
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3275,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3274])).

fof(f3274,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3090])).

fof(f3090,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3089])).

fof(f3089,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3027])).

fof(f3027,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_yellow_0)).

fof(f3832,plain,
    ( r1_yellow_0(sK4,sK5)
    | ~ spl50_2 ),
    inference(avatar_component_clause,[],[f3831])).

fof(f3831,plain,
    ( spl50_2
  <=> r1_yellow_0(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_2])])).

fof(f3829,plain,
    ( ~ r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | spl50_1 ),
    inference(avatar_component_clause,[],[f3827])).

fof(f3827,plain,
    ( spl50_1
  <=> r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_1])])).

fof(f20185,plain,
    ( ~ m1_subset_1(sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl50_296
    | ~ spl50_297 ),
    inference(subsumption_resolution,[],[f20165,f17917])).

fof(f17917,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | ~ spl50_297 ),
    inference(avatar_component_clause,[],[f17915])).

fof(f17915,plain,
    ( spl50_297
  <=> r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_297])])).

fof(f20165,plain,
    ( ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | ~ m1_subset_1(sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl50_296 ),
    inference(resolution,[],[f17912,f3500])).

fof(f3500,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3094])).

fof(f3094,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3093])).

fof(f3093,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3034])).

fof(f3034,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow_0)).

fof(f17912,plain,
    ( ~ r2_lattice3(sK4,sK5,sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | spl50_296 ),
    inference(avatar_component_clause,[],[f17911])).

fof(f17911,plain,
    ( spl50_296
  <=> r2_lattice3(sK4,sK5,sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_296])])).

fof(f20102,plain,
    ( spl50_1
    | ~ spl50_2
    | ~ spl50_296
    | spl50_297 ),
    inference(avatar_contradiction_clause,[],[f20101])).

fof(f20101,plain,
    ( $false
    | spl50_1
    | ~ spl50_2
    | ~ spl50_296
    | spl50_297 ),
    inference(subsumption_resolution,[],[f20100,f3386])).

fof(f20100,plain,
    ( v2_struct_0(sK4)
    | spl50_1
    | ~ spl50_2
    | ~ spl50_296
    | spl50_297 ),
    inference(subsumption_resolution,[],[f20099,f3387])).

fof(f20099,plain,
    ( ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl50_1
    | ~ spl50_2
    | ~ spl50_296
    | spl50_297 ),
    inference(subsumption_resolution,[],[f20098,f17894])).

fof(f20098,plain,
    ( ~ m1_subset_1(sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl50_296
    | spl50_297 ),
    inference(subsumption_resolution,[],[f20053,f17916])).

fof(f17916,plain,
    ( ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | spl50_297 ),
    inference(avatar_component_clause,[],[f17915])).

fof(f20053,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | ~ m1_subset_1(sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl50_296 ),
    inference(resolution,[],[f17913,f3499])).

fof(f3499,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3094])).

fof(f17913,plain,
    ( r2_lattice3(sK4,sK5,sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | ~ spl50_296 ),
    inference(avatar_component_clause,[],[f17911])).

fof(f17919,plain,
    ( ~ spl50_296
    | ~ spl50_297
    | spl50_1
    | ~ spl50_2 ),
    inference(avatar_split_clause,[],[f17896,f3831,f3827,f17915,f17911])).

fof(f17896,plain,
    ( ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | ~ r2_lattice3(sK4,sK5,sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | spl50_1
    | ~ spl50_2 ),
    inference(resolution,[],[f3829,f14690])).

fof(f14690,plain,
    ( ! [X3] :
        ( r1_yellow_0(sK4,X3)
        | ~ r2_lattice3(sK4,X3,sK13(sK4,sK5,X3))
        | ~ r2_lattice3(sK4,sK5,sK13(sK4,sK5,X3)) )
    | ~ spl50_2 ),
    inference(subsumption_resolution,[],[f14689,f3386])).

fof(f14689,plain,
    ( ! [X3] :
        ( r1_yellow_0(sK4,X3)
        | ~ r2_lattice3(sK4,X3,sK13(sK4,sK5,X3))
        | ~ r2_lattice3(sK4,sK5,sK13(sK4,sK5,X3))
        | v2_struct_0(sK4) )
    | ~ spl50_2 ),
    inference(subsumption_resolution,[],[f14685,f3387])).

fof(f14685,plain,
    ( ! [X3] :
        ( r1_yellow_0(sK4,X3)
        | ~ r2_lattice3(sK4,X3,sK13(sK4,sK5,X3))
        | ~ r2_lattice3(sK4,sK5,sK13(sK4,sK5,X3))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl50_2 ),
    inference(resolution,[],[f3832,f3476])).

fof(f3476,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK13(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK13(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3277])).

fof(f17918,plain,
    ( spl50_296
    | spl50_297
    | spl50_1
    | ~ spl50_2 ),
    inference(avatar_split_clause,[],[f17895,f3831,f3827,f17915,f17911])).

fof(f17895,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | r2_lattice3(sK4,sK5,sK13(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | spl50_1
    | ~ spl50_2 ),
    inference(resolution,[],[f3829,f14688])).

fof(f14688,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK4,X2)
        | r2_lattice3(sK4,X2,sK13(sK4,sK5,X2))
        | r2_lattice3(sK4,sK5,sK13(sK4,sK5,X2)) )
    | ~ spl50_2 ),
    inference(subsumption_resolution,[],[f14687,f3386])).

fof(f14687,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK4,X2)
        | r2_lattice3(sK4,X2,sK13(sK4,sK5,X2))
        | r2_lattice3(sK4,sK5,sK13(sK4,sK5,X2))
        | v2_struct_0(sK4) )
    | ~ spl50_2 ),
    inference(subsumption_resolution,[],[f14684,f3387])).

fof(f14684,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK4,X2)
        | r2_lattice3(sK4,X2,sK13(sK4,sK5,X2))
        | r2_lattice3(sK4,sK5,sK13(sK4,sK5,X2))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl50_2 ),
    inference(resolution,[],[f3832,f3475])).

fof(f3475,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK13(X0,X1,X2))
      | r2_lattice3(X0,X1,sK13(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3277])).

fof(f17874,plain,
    ( ~ spl50_273
    | spl50_3
    | ~ spl50_4 ),
    inference(avatar_split_clause,[],[f17873,f3839,f3835,f17048])).

fof(f17048,plain,
    ( spl50_273
  <=> r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_273])])).

fof(f3835,plain,
    ( spl50_3
  <=> r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_3])])).

fof(f3839,plain,
    ( spl50_4
  <=> r2_yellow_0(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_4])])).

fof(f17873,plain,
    ( ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | spl50_3
    | ~ spl50_4 ),
    inference(subsumption_resolution,[],[f17064,f17397])).

fof(f17397,plain,
    ( ! [X55] :
        ( r1_lattice3(sK4,X55,sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ r1_lattice3(sK4,k3_xboole_0(X55,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4)))) )
    | spl50_3
    | ~ spl50_4 ),
    inference(subsumption_resolution,[],[f17396,f3386])).

fof(f17396,plain,
    ( ! [X55] :
        ( r1_lattice3(sK4,X55,sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ r1_lattice3(sK4,k3_xboole_0(X55,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | v2_struct_0(sK4) )
    | spl50_3
    | ~ spl50_4 ),
    inference(subsumption_resolution,[],[f17292,f3387])).

fof(f17292,plain,
    ( ! [X55] :
        ( r1_lattice3(sK4,X55,sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ r1_lattice3(sK4,k3_xboole_0(X55,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl50_3
    | ~ spl50_4 ),
    inference(resolution,[],[f16147,f3502])).

fof(f3502,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3094])).

fof(f16147,plain,
    ( m1_subset_1(sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
    | spl50_3
    | ~ spl50_4 ),
    inference(resolution,[],[f16131,f3840])).

fof(f3840,plain,
    ( r2_yellow_0(sK4,sK5)
    | ~ spl50_4 ),
    inference(avatar_component_clause,[],[f3839])).

fof(f16131,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK4,X1)
        | m1_subset_1(sK6(sK4,X1,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4)) )
    | spl50_3 ),
    inference(subsumption_resolution,[],[f16130,f3386])).

fof(f16130,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK4,X1)
        | m1_subset_1(sK6(sK4,X1,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
        | v2_struct_0(sK4) )
    | spl50_3 ),
    inference(subsumption_resolution,[],[f16117,f3387])).

fof(f16117,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK4,X1)
        | m1_subset_1(sK6(sK4,X1,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl50_3 ),
    inference(resolution,[],[f3837,f3404])).

fof(f3404,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3258])).

fof(f3258,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK6(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK6(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK6(X0,X1,X2))
              | r1_lattice3(X0,X1,sK6(X0,X1,X2)) )
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3256,f3257])).

fof(f3257,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK6(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK6(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK6(X0,X1,X2))
          | r1_lattice3(X0,X1,sK6(X0,X1,X2)) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3256,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3255])).

fof(f3255,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3058])).

fof(f3058,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3057])).

fof(f3057,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3029])).

fof(f3029,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_yellow_0)).

fof(f3837,plain,
    ( ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | spl50_3 ),
    inference(avatar_component_clause,[],[f3835])).

fof(f17064,plain,
    ( ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | ~ r1_lattice3(sK4,sK5,sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | spl50_3
    | ~ spl50_4 ),
    inference(resolution,[],[f16135,f3840])).

fof(f16135,plain,
    ( ! [X3] :
        ( ~ r2_yellow_0(sK4,X3)
        | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,X3,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ r1_lattice3(sK4,X3,sK6(sK4,X3,k3_xboole_0(sK5,u1_struct_0(sK4)))) )
    | spl50_3 ),
    inference(subsumption_resolution,[],[f16134,f3386])).

fof(f16134,plain,
    ( ! [X3] :
        ( ~ r2_yellow_0(sK4,X3)
        | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,X3,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ r1_lattice3(sK4,X3,sK6(sK4,X3,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | v2_struct_0(sK4) )
    | spl50_3 ),
    inference(subsumption_resolution,[],[f16119,f3387])).

fof(f16119,plain,
    ( ! [X3] :
        ( ~ r2_yellow_0(sK4,X3)
        | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,X3,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ r1_lattice3(sK4,X3,sK6(sK4,X3,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl50_3 ),
    inference(resolution,[],[f3837,f3406])).

fof(f3406,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3258])).

fof(f17863,plain,
    ( spl50_3
    | ~ spl50_4
    | ~ spl50_272
    | spl50_273 ),
    inference(avatar_contradiction_clause,[],[f17862])).

fof(f17862,plain,
    ( $false
    | spl50_3
    | ~ spl50_4
    | ~ spl50_272
    | spl50_273 ),
    inference(subsumption_resolution,[],[f17861,f3386])).

fof(f17861,plain,
    ( v2_struct_0(sK4)
    | spl50_3
    | ~ spl50_4
    | ~ spl50_272
    | spl50_273 ),
    inference(subsumption_resolution,[],[f17860,f3387])).

fof(f17860,plain,
    ( ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl50_3
    | ~ spl50_4
    | ~ spl50_272
    | spl50_273 ),
    inference(subsumption_resolution,[],[f17859,f16147])).

fof(f17859,plain,
    ( ~ m1_subset_1(sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl50_272
    | spl50_273 ),
    inference(subsumption_resolution,[],[f17814,f17049])).

fof(f17049,plain,
    ( ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | spl50_273 ),
    inference(avatar_component_clause,[],[f17048])).

fof(f17814,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl50_272 ),
    inference(resolution,[],[f17046,f3501])).

fof(f3501,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3094])).

fof(f17046,plain,
    ( r1_lattice3(sK4,sK5,sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | ~ spl50_272 ),
    inference(avatar_component_clause,[],[f17044])).

fof(f17044,plain,
    ( spl50_272
  <=> r1_lattice3(sK4,sK5,sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_272])])).

fof(f17051,plain,
    ( spl50_272
    | spl50_273
    | spl50_3
    | ~ spl50_4 ),
    inference(avatar_split_clause,[],[f17037,f3839,f3835,f17048,f17044])).

fof(f17037,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | r1_lattice3(sK4,sK5,sK6(sK4,sK5,k3_xboole_0(sK5,u1_struct_0(sK4))))
    | spl50_3
    | ~ spl50_4 ),
    inference(resolution,[],[f16133,f3840])).

fof(f16133,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK4,X2)
        | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,X2,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | r1_lattice3(sK4,X2,sK6(sK4,X2,k3_xboole_0(sK5,u1_struct_0(sK4)))) )
    | spl50_3 ),
    inference(subsumption_resolution,[],[f16132,f3386])).

fof(f16132,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK4,X2)
        | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,X2,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | r1_lattice3(sK4,X2,sK6(sK4,X2,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | v2_struct_0(sK4) )
    | spl50_3 ),
    inference(subsumption_resolution,[],[f16118,f3387])).

fof(f16118,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK4,X2)
        | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,X2,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | r1_lattice3(sK4,X2,sK6(sK4,X2,k3_xboole_0(sK5,u1_struct_0(sK4))))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl50_3 ),
    inference(resolution,[],[f3837,f3405])).

fof(f3405,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3258])).

fof(f16098,plain,
    ( ~ spl50_3
    | spl50_4
    | ~ spl50_220 ),
    inference(avatar_split_clause,[],[f16097,f14718,f3839,f3835])).

fof(f14718,plain,
    ( spl50_220
  <=> r1_lattice3(sK4,sK5,sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_220])])).

fof(f16097,plain,
    ( r2_yellow_0(sK4,sK5)
    | ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | ~ spl50_220 ),
    inference(subsumption_resolution,[],[f16096,f5411])).

fof(f5411,plain,(
    ! [X17,X16] :
      ( r1_lattice3(sK4,k3_xboole_0(X16,u1_struct_0(sK4)),sK6(sK4,X17,X16))
      | r2_yellow_0(sK4,X16)
      | ~ r2_yellow_0(sK4,X17)
      | r1_lattice3(sK4,X17,sK6(sK4,X17,X16)) ) ),
    inference(subsumption_resolution,[],[f5410,f3856])).

fof(f3856,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK4,X1)
      | r2_yellow_0(sK4,X0)
      | m1_subset_1(sK6(sK4,X1,X0),u1_struct_0(sK4)) ) ),
    inference(subsumption_resolution,[],[f3846,f3387])).

fof(f3846,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(sK4,X0)
      | ~ r2_yellow_0(sK4,X1)
      | m1_subset_1(sK6(sK4,X1,X0),u1_struct_0(sK4))
      | ~ l1_orders_2(sK4) ) ),
    inference(resolution,[],[f3386,f3404])).

fof(f5410,plain,(
    ! [X17,X16] :
      ( r1_lattice3(sK4,k3_xboole_0(X16,u1_struct_0(sK4)),sK6(sK4,X17,X16))
      | ~ m1_subset_1(sK6(sK4,X17,X16),u1_struct_0(sK4))
      | r2_yellow_0(sK4,X16)
      | ~ r2_yellow_0(sK4,X17)
      | r1_lattice3(sK4,X17,sK6(sK4,X17,X16)) ) ),
    inference(subsumption_resolution,[],[f5409,f3386])).

fof(f5409,plain,(
    ! [X17,X16] :
      ( r1_lattice3(sK4,k3_xboole_0(X16,u1_struct_0(sK4)),sK6(sK4,X17,X16))
      | ~ m1_subset_1(sK6(sK4,X17,X16),u1_struct_0(sK4))
      | r2_yellow_0(sK4,X16)
      | ~ r2_yellow_0(sK4,X17)
      | r1_lattice3(sK4,X17,sK6(sK4,X17,X16))
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f5376,f3387])).

fof(f5376,plain,(
    ! [X17,X16] :
      ( r1_lattice3(sK4,k3_xboole_0(X16,u1_struct_0(sK4)),sK6(sK4,X17,X16))
      | ~ m1_subset_1(sK6(sK4,X17,X16),u1_struct_0(sK4))
      | r2_yellow_0(sK4,X16)
      | ~ r2_yellow_0(sK4,X17)
      | r1_lattice3(sK4,X17,sK6(sK4,X17,X16))
      | ~ l1_orders_2(sK4)
      | v2_struct_0(sK4) ) ),
    inference(resolution,[],[f3864,f3405])).

fof(f3864,plain,(
    ! [X17,X16] :
      ( ~ r1_lattice3(sK4,X16,X17)
      | r1_lattice3(sK4,k3_xboole_0(X16,u1_struct_0(sK4)),X17)
      | ~ m1_subset_1(X17,u1_struct_0(sK4)) ) ),
    inference(subsumption_resolution,[],[f3854,f3387])).

fof(f3854,plain,(
    ! [X17,X16] :
      ( r1_lattice3(sK4,k3_xboole_0(X16,u1_struct_0(sK4)),X17)
      | ~ r1_lattice3(sK4,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(sK4))
      | ~ l1_orders_2(sK4) ) ),
    inference(resolution,[],[f3386,f3501])).

fof(f16096,plain,
    ( r2_yellow_0(sK4,sK5)
    | ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ spl50_220 ),
    inference(subsumption_resolution,[],[f16095,f3386])).

fof(f16095,plain,
    ( r2_yellow_0(sK4,sK5)
    | ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | v2_struct_0(sK4)
    | ~ spl50_220 ),
    inference(subsumption_resolution,[],[f15888,f3387])).

fof(f15888,plain,
    ( r2_yellow_0(sK4,sK5)
    | ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl50_220 ),
    inference(resolution,[],[f14720,f3406])).

fof(f14720,plain,
    ( r1_lattice3(sK4,sK5,sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ spl50_220 ),
    inference(avatar_component_clause,[],[f14718])).

fof(f15796,plain,
    ( ~ spl50_3
    | spl50_4
    | ~ spl50_219
    | spl50_220 ),
    inference(avatar_contradiction_clause,[],[f15795])).

fof(f15795,plain,
    ( $false
    | ~ spl50_3
    | spl50_4
    | ~ spl50_219
    | spl50_220 ),
    inference(subsumption_resolution,[],[f15794,f3386])).

fof(f15794,plain,
    ( v2_struct_0(sK4)
    | ~ spl50_3
    | spl50_4
    | ~ spl50_219
    | spl50_220 ),
    inference(subsumption_resolution,[],[f15793,f3387])).

fof(f15793,plain,
    ( ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl50_3
    | spl50_4
    | ~ spl50_219
    | spl50_220 ),
    inference(subsumption_resolution,[],[f15792,f14697])).

fof(f14697,plain,
    ( m1_subset_1(sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5),u1_struct_0(sK4))
    | ~ spl50_3
    | spl50_4 ),
    inference(resolution,[],[f3836,f4224])).

fof(f4224,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK4,X1)
        | m1_subset_1(sK6(sK4,X1,sK5),u1_struct_0(sK4)) )
    | spl50_4 ),
    inference(subsumption_resolution,[],[f4223,f3386])).

fof(f4223,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK4,X1)
        | m1_subset_1(sK6(sK4,X1,sK5),u1_struct_0(sK4))
        | v2_struct_0(sK4) )
    | spl50_4 ),
    inference(subsumption_resolution,[],[f4218,f3387])).

fof(f4218,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK4,X1)
        | m1_subset_1(sK6(sK4,X1,sK5),u1_struct_0(sK4))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl50_4 ),
    inference(resolution,[],[f3841,f3404])).

fof(f3841,plain,
    ( ~ r2_yellow_0(sK4,sK5)
    | spl50_4 ),
    inference(avatar_component_clause,[],[f3839])).

fof(f3836,plain,
    ( r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | ~ spl50_3 ),
    inference(avatar_component_clause,[],[f3835])).

fof(f15792,plain,
    ( ~ m1_subset_1(sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl50_219
    | spl50_220 ),
    inference(subsumption_resolution,[],[f15772,f14716])).

fof(f14716,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ spl50_219 ),
    inference(avatar_component_clause,[],[f14714])).

fof(f14714,plain,
    ( spl50_219
  <=> r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_219])])).

fof(f15772,plain,
    ( ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ m1_subset_1(sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl50_220 ),
    inference(resolution,[],[f14719,f3502])).

fof(f14719,plain,
    ( ~ r1_lattice3(sK4,sK5,sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | spl50_220 ),
    inference(avatar_component_clause,[],[f14718])).

fof(f14721,plain,
    ( spl50_219
    | spl50_220
    | ~ spl50_3
    | spl50_4 ),
    inference(avatar_split_clause,[],[f14698,f3839,f3835,f14718,f14714])).

fof(f14698,plain,
    ( r1_lattice3(sK4,sK5,sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ spl50_3
    | spl50_4 ),
    inference(resolution,[],[f3836,f4226])).

fof(f4226,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK4,X2)
        | r1_lattice3(sK4,sK5,sK6(sK4,X2,sK5))
        | r1_lattice3(sK4,X2,sK6(sK4,X2,sK5)) )
    | spl50_4 ),
    inference(subsumption_resolution,[],[f4225,f3386])).

fof(f4225,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK4,X2)
        | r1_lattice3(sK4,sK5,sK6(sK4,X2,sK5))
        | r1_lattice3(sK4,X2,sK6(sK4,X2,sK5))
        | v2_struct_0(sK4) )
    | spl50_4 ),
    inference(subsumption_resolution,[],[f4219,f3387])).

fof(f4219,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK4,X2)
        | r1_lattice3(sK4,sK5,sK6(sK4,X2,sK5))
        | r1_lattice3(sK4,X2,sK6(sK4,X2,sK5))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl50_4 ),
    inference(resolution,[],[f3841,f3405])).

fof(f14679,plain,
    ( ~ spl50_85
    | ~ spl50_1
    | spl50_2 ),
    inference(avatar_split_clause,[],[f14678,f3831,f3827,f8232])).

fof(f8232,plain,
    ( spl50_85
  <=> r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl50_85])])).

fof(f14678,plain,
    ( ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ spl50_1
    | spl50_2 ),
    inference(subsumption_resolution,[],[f10442,f14482])).

fof(f14482,plain,
    ( ! [X53] :
        ( r2_lattice3(sK4,X53,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | ~ r2_lattice3(sK4,k3_xboole_0(X53,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5)) )
    | ~ spl50_1
    | spl50_2 ),
    inference(subsumption_resolution,[],[f14481,f3386])).

fof(f14481,plain,
    ( ! [X53] :
        ( r2_lattice3(sK4,X53,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | ~ r2_lattice3(sK4,k3_xboole_0(X53,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | v2_struct_0(sK4) )
    | ~ spl50_1
    | spl50_2 ),
    inference(subsumption_resolution,[],[f14379,f3387])).

fof(f14379,plain,
    ( ! [X53] :
        ( r2_lattice3(sK4,X53,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | ~ r2_lattice3(sK4,k3_xboole_0(X53,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl50_1
    | spl50_2 ),
    inference(resolution,[],[f4656,f3500])).

fof(f4656,plain,
    ( m1_subset_1(sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5),u1_struct_0(sK4))
    | ~ spl50_1
    | spl50_2 ),
    inference(resolution,[],[f4210,f3828])).

fof(f3828,plain,
    ( r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | ~ spl50_1 ),
    inference(avatar_component_clause,[],[f3827])).

fof(f4210,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK4,X0)
        | m1_subset_1(sK13(sK4,X0,sK5),u1_struct_0(sK4)) )
    | spl50_2 ),
    inference(subsumption_resolution,[],[f4209,f3386])).

fof(f4209,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK4,X0)
        | m1_subset_1(sK13(sK4,X0,sK5),u1_struct_0(sK4))
        | v2_struct_0(sK4) )
    | spl50_2 ),
    inference(subsumption_resolution,[],[f4204,f3387])).

fof(f4204,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK4,X0)
        | m1_subset_1(sK13(sK4,X0,sK5),u1_struct_0(sK4))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl50_2 ),
    inference(resolution,[],[f3833,f3474])).

fof(f3833,plain,
    ( ~ r1_yellow_0(sK4,sK5)
    | spl50_2 ),
    inference(avatar_component_clause,[],[f3831])).

fof(f10442,plain,
    ( ~ r2_lattice3(sK4,sK5,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ spl50_1
    | spl50_2 ),
    inference(resolution,[],[f4148,f3833])).

fof(f4148,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK4,X2)
        | ~ r2_lattice3(sK4,X2,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X2))
        | ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X2)) )
    | ~ spl50_1 ),
    inference(subsumption_resolution,[],[f4147,f3386])).

fof(f4147,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK4,X2)
        | ~ r2_lattice3(sK4,X2,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X2))
        | ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X2))
        | v2_struct_0(sK4) )
    | ~ spl50_1 ),
    inference(subsumption_resolution,[],[f4132,f3387])).

fof(f4132,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK4,X2)
        | ~ r2_lattice3(sK4,X2,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X2))
        | ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X2))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl50_1 ),
    inference(resolution,[],[f3828,f3476])).

fof(f14675,plain,
    ( spl50_85
    | ~ spl50_1
    | spl50_2 ),
    inference(avatar_split_clause,[],[f14674,f3831,f3827,f8232])).

fof(f14674,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ spl50_1
    | spl50_2 ),
    inference(subsumption_resolution,[],[f10370,f14480])).

fof(f14480,plain,
    ( ! [X52] :
        ( r2_lattice3(sK4,k3_xboole_0(X52,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | ~ r2_lattice3(sK4,X52,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5)) )
    | ~ spl50_1
    | spl50_2 ),
    inference(subsumption_resolution,[],[f14479,f3386])).

fof(f14479,plain,
    ( ! [X52] :
        ( r2_lattice3(sK4,k3_xboole_0(X52,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | ~ r2_lattice3(sK4,X52,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | v2_struct_0(sK4) )
    | ~ spl50_1
    | spl50_2 ),
    inference(subsumption_resolution,[],[f14378,f3387])).

fof(f14378,plain,
    ( ! [X52] :
        ( r2_lattice3(sK4,k3_xboole_0(X52,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | ~ r2_lattice3(sK4,X52,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl50_1
    | spl50_2 ),
    inference(resolution,[],[f4656,f3499])).

fof(f10370,plain,
    ( r2_lattice3(sK4,sK5,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK5))
    | ~ spl50_1
    | spl50_2 ),
    inference(resolution,[],[f4146,f3833])).

fof(f4146,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK4,X1)
        | r2_lattice3(sK4,X1,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X1))
        | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X1)) )
    | ~ spl50_1 ),
    inference(subsumption_resolution,[],[f4145,f3386])).

fof(f4145,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK4,X1)
        | r2_lattice3(sK4,X1,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X1))
        | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X1))
        | v2_struct_0(sK4) )
    | ~ spl50_1 ),
    inference(subsumption_resolution,[],[f4131,f3387])).

fof(f4131,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK4,X1)
        | r2_lattice3(sK4,X1,sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X1))
        | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK13(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),X1))
        | ~ l1_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl50_1 ),
    inference(resolution,[],[f3828,f3475])).

fof(f3845,plain,
    ( spl50_2
    | spl50_1
    | spl50_4
    | spl50_3 ),
    inference(avatar_split_clause,[],[f3388,f3835,f3839,f3827,f3831])).

fof(f3388,plain,
    ( r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | r2_yellow_0(sK4,sK5)
    | r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | r1_yellow_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f3254])).

fof(f3844,plain,
    ( ~ spl50_1
    | ~ spl50_2
    | spl50_4
    | spl50_3 ),
    inference(avatar_split_clause,[],[f3391,f3835,f3839,f3831,f3827])).

fof(f3391,plain,
    ( r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | r2_yellow_0(sK4,sK5)
    | ~ r1_yellow_0(sK4,sK5)
    | ~ r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f3254])).

fof(f3843,plain,
    ( spl50_2
    | spl50_1
    | ~ spl50_3
    | ~ spl50_4 ),
    inference(avatar_split_clause,[],[f3400,f3839,f3835,f3827,f3831])).

fof(f3400,plain,
    ( ~ r2_yellow_0(sK4,sK5)
    | ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | r1_yellow_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f3254])).

fof(f3842,plain,
    ( ~ spl50_1
    | ~ spl50_2
    | ~ spl50_3
    | ~ spl50_4 ),
    inference(avatar_split_clause,[],[f3403,f3839,f3835,f3831,f3827])).

fof(f3403,plain,
    ( ~ r2_yellow_0(sK4,sK5)
    | ~ r2_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)))
    | ~ r1_yellow_0(sK4,sK5)
    | ~ r1_yellow_0(sK4,k3_xboole_0(sK5,u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f3254])).
%------------------------------------------------------------------------------
