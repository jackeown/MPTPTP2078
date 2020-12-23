%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1999+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:02 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 934 expanded)
%              Number of leaves         :   35 ( 328 expanded)
%              Depth                    :   41
%              Number of atoms          : 1360 (13795 expanded)
%              Number of equality atoms :   38 (  61 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f749,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f132,f137,f142,f147,f151,f289,f626,f629,f723,f748])).

fof(f748,plain,(
    ~ spl12_16 ),
    inference(avatar_contradiction_clause,[],[f747])).

fof(f747,plain,
    ( $false
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f746,f77])).

fof(f77,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ( ~ r3_orders_2(sK4,sK7,sK5)
        & ~ r3_orders_2(sK4,sK6,sK5)
        & r1_waybel_3(sK4,k12_lattice3(sK4,sK6,sK7),sK5)
        & m1_subset_1(sK7,u1_struct_0(sK4))
        & m1_subset_1(sK6,u1_struct_0(sK4)) )
      | ~ v4_waybel_7(sK5,sK4) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r3_orders_2(sK4,X5,sK5)
              | r3_orders_2(sK4,X4,sK5)
              | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),sK5)
              | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
          | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
      | v4_waybel_7(sK5,sK4) )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & v5_waybel_7(k1_waybel_4(sK4),sK4)
    & l1_orders_2(sK4)
    & v3_waybel_3(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v1_yellow_0(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f46,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X3,X1)
                      & ~ r3_orders_2(X0,X2,X1)
                      & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X5,X1)
                      | r3_orders_2(X0,X4,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v4_waybel_7(X1,X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & v5_waybel_7(k1_waybel_4(X0),X0)
        & l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(sK4,X3,X1)
                    & ~ r3_orders_2(sK4,X2,X1)
                    & r1_waybel_3(sK4,k12_lattice3(sK4,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(sK4)) )
                & m1_subset_1(X2,u1_struct_0(sK4)) )
            | ~ v4_waybel_7(X1,sK4) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r3_orders_2(sK4,X5,X1)
                    | r3_orders_2(sK4,X4,X1)
                    | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),X1)
                    | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
                | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
            | v4_waybel_7(X1,sK4) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & v5_waybel_7(k1_waybel_4(sK4),sK4)
      & l1_orders_2(sK4)
      & v3_waybel_3(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v1_yellow_0(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(sK4,X3,X1)
                  & ~ r3_orders_2(sK4,X2,X1)
                  & r1_waybel_3(sK4,k12_lattice3(sK4,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(sK4)) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          | ~ v4_waybel_7(X1,sK4) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r3_orders_2(sK4,X5,X1)
                  | r3_orders_2(sK4,X4,X1)
                  | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),X1)
                  | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
              | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
          | v4_waybel_7(X1,sK4) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_orders_2(sK4,X3,sK5)
                & ~ r3_orders_2(sK4,X2,sK5)
                & r1_waybel_3(sK4,k12_lattice3(sK4,X2,X3),sK5)
                & m1_subset_1(X3,u1_struct_0(sK4)) )
            & m1_subset_1(X2,u1_struct_0(sK4)) )
        | ~ v4_waybel_7(sK5,sK4) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r3_orders_2(sK4,X5,sK5)
                | r3_orders_2(sK4,X4,sK5)
                | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),sK5)
                | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
            | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
        | v4_waybel_7(sK5,sK4) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r3_orders_2(sK4,X3,sK5)
            & ~ r3_orders_2(sK4,X2,sK5)
            & r1_waybel_3(sK4,k12_lattice3(sK4,X2,X3),sK5)
            & m1_subset_1(X3,u1_struct_0(sK4)) )
        & m1_subset_1(X2,u1_struct_0(sK4)) )
   => ( ? [X3] :
          ( ~ r3_orders_2(sK4,X3,sK5)
          & ~ r3_orders_2(sK4,sK6,sK5)
          & r1_waybel_3(sK4,k12_lattice3(sK4,sK6,X3),sK5)
          & m1_subset_1(X3,u1_struct_0(sK4)) )
      & m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ~ r3_orders_2(sK4,X3,sK5)
        & ~ r3_orders_2(sK4,sK6,sK5)
        & r1_waybel_3(sK4,k12_lattice3(sK4,sK6,X3),sK5)
        & m1_subset_1(X3,u1_struct_0(sK4)) )
   => ( ~ r3_orders_2(sK4,sK7,sK5)
      & ~ r3_orders_2(sK4,sK6,sK5)
      & r1_waybel_3(sK4,k12_lattice3(sK4,sK6,sK7),sK5)
      & m1_subset_1(sK7,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X3,X1)
                    & ~ r3_orders_2(X0,X2,X1)
                    & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v4_waybel_7(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r3_orders_2(X0,X5,X1)
                    | r3_orders_2(X0,X4,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v4_waybel_7(X1,X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X3,X1)
                    & ~ r3_orders_2(X0,X2,X1)
                    & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v4_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v4_waybel_7(X1,X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X3,X1)
                    & ~ r3_orders_2(X0,X2,X1)
                    & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v4_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v4_waybel_7(X1,X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_waybel_7(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_waybel_7(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v5_waybel_7(k1_waybel_4(X0),X0)
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ( v4_waybel_7(X1,X0)
              <=> ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ~ r3_orders_2(X0,X3,X1)
                            & ~ r3_orders_2(X0,X2,X1)
                            & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v5_waybel_7(k1_waybel_4(X0),X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_waybel_7)).

fof(f746,plain,
    ( ~ l1_orders_2(sK4)
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f745,f75])).

fof(f75,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f745,plain,
    ( ~ v2_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ spl12_16 ),
    inference(resolution,[],[f621,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f621,plain,
    ( v2_struct_0(sK4)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl12_16
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f723,plain,
    ( ~ spl12_1
    | spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | spl12_14 ),
    inference(avatar_contradiction_clause,[],[f722])).

fof(f722,plain,
    ( $false
    | ~ spl12_1
    | spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | spl12_14 ),
    inference(subsumption_resolution,[],[f721,f126])).

fof(f126,plain,
    ( ~ r3_orders_2(sK4,sK7,sK5)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl12_2
  <=> r3_orders_2(sK4,sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f721,plain,
    ( r3_orders_2(sK4,sK7,sK5)
    | ~ spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | spl12_14 ),
    inference(subsumption_resolution,[],[f693,f131])).

fof(f131,plain,
    ( ~ r3_orders_2(sK4,sK6,sK5)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl12_3
  <=> r3_orders_2(sK4,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f693,plain,
    ( r3_orders_2(sK4,sK6,sK5)
    | r3_orders_2(sK4,sK7,sK5)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | spl12_14 ),
    inference(resolution,[],[f682,f468])).

fof(f468,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,k2_tarski(X2,X3))
      | r3_orders_2(X1,X2,X0)
      | r3_orders_2(X1,X3,X0) ) ),
    inference(resolution,[],[f457,f118])).

fof(f118,plain,(
    ! [X0,X1] : sP3(X0,X1,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f42,f41])).

fof(f41,plain,(
    ! [X3,X1,X0] :
      ( sP2(X3,X1,X0)
    <=> ( X1 = X3
        | X0 = X3 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f457,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ sP3(X13,X14,X12)
      | ~ sP1(X10,X11,X12)
      | r3_orders_2(X11,X13,X10)
      | r3_orders_2(X11,X14,X10) ) ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( r3_orders_2(X11,X13,X10)
      | ~ sP1(X10,X11,X12)
      | ~ sP1(X10,X11,X12)
      | ~ sP3(X13,X14,X12)
      | r3_orders_2(X11,X14,X10) ) ),
    inference(superposition,[],[f99,f194])).

fof(f194,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( sK10(X7,X8,X9) = X11
      | ~ sP1(X7,X8,X9)
      | ~ sP3(X11,X10,X9)
      | r3_orders_2(X8,X10,X7) ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( r3_orders_2(X8,X10,X7)
      | ~ sP1(X7,X8,X9)
      | ~ sP3(X11,X10,X9)
      | sK10(X7,X8,X9) = X11
      | ~ sP1(X7,X8,X9) ) ),
    inference(superposition,[],[f99,f174])).

fof(f174,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK10(X0,X1,X2) = X4
      | ~ sP3(X3,X4,X2)
      | sK10(X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(resolution,[],[f173,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( X0 != X1
          & X0 != X2 ) )
      & ( X0 = X1
        | X0 = X2
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X3,X1,X0] :
      ( ( sP2(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP2(X3,X1,X0) ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X3,X1,X0] :
      ( ( sP2(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP2(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f173,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP2(sK10(X3,X4,X2),X1,X0)
      | ~ sP1(X3,X4,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(superposition,[],[f162,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(sK10(X0,X1,k2_tarski(X2,X3)),X3,X2)
      | ~ sP1(X0,X1,k2_tarski(X2,X3)) ) ),
    inference(resolution,[],[f161,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X1,sK10(X0,X1,X2),X0)
        & r2_hidden(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r3_orders_2(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,sK10(X0,X1,X2),X0)
        & r2_hidden(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r3_orders_2(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( r3_orders_2(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( r3_orders_2(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
      | sP2(X0,X2,X1) ) ),
    inference(resolution,[],[f107,f118])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP2(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(sK11(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( sP2(sK11(X0,X1,X2),X1,X0)
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X4,X1,X0) )
            & ( sP2(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(sK11(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( sP2(sK11(X0,X1,X2),X1,X0)
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X4,X1,X0) )
            & ( sP2(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X3,X1,X0) )
            & ( sP2(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X1,sK10(X0,X1,X2),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f682,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | spl12_14 ),
    inference(subsumption_resolution,[],[f681,f607])).

fof(f607,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl12_14 ),
    inference(avatar_component_clause,[],[f606])).

fof(f606,plain,
    ( spl12_14
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f681,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f680,f146])).

fof(f146,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl12_6
  <=> m1_subset_1(sK6,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f680,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f679,f141])).

fof(f141,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl12_5
  <=> m1_subset_1(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f679,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f678,f70])).

fof(f70,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f678,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f677,f71])).

fof(f71,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f677,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f676,f72])).

fof(f72,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f676,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f675,f74])).

fof(f74,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f675,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f674,f75])).

fof(f674,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f673,f76])).

fof(f76,plain,(
    v3_waybel_3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f673,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f672,f77])).

fof(f672,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f671,f79])).

fof(f79,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f671,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f667,f121])).

fof(f121,plain,
    ( v4_waybel_7(sK5,sK4)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl12_1
  <=> v4_waybel_7(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f667,plain,
    ( sP1(sK5,sK4,k2_tarski(sK6,sK7))
    | ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_4 ),
    inference(resolution,[],[f492,f136])).

fof(f136,plain,
    ( r1_waybel_3(sK4,k12_lattice3(sK4,sK6,sK7),sK5)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl12_4
  <=> r1_waybel_3(sK4,k12_lattice3(sK4,sK6,sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f492,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_3(X0,k12_lattice3(X0,X1,X2),X3)
      | sP1(X3,X0,k2_tarski(X1,X2))
      | ~ v4_waybel_7(X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f491,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f105,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f491,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_3(X0,k12_lattice3(X0,X1,X2),X3)
      | sP1(X3,X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_waybel_7(X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f490,f103])).

fof(f103,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f490,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_3(X0,k12_lattice3(X0,X1,X2),X3)
      | sP1(X3,X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_tarski(X1,X2))
      | ~ v4_waybel_7(X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f489,f104])).

fof(f104,plain,(
    ! [X0,X1] : v1_finset_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_finset_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_finset_1)).

fof(f489,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_3(X0,k12_lattice3(X0,X1,X2),X3)
      | sP1(X3,X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(k2_tarski(X1,X2))
      | v1_xboole_0(k2_tarski(X1,X2))
      | ~ v4_waybel_7(X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f488])).

fof(f488,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_3(X0,k12_lattice3(X0,X1,X2),X3)
      | sP1(X3,X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(k2_tarski(X1,X2))
      | v1_xboole_0(k2_tarski(X1,X2))
      | ~ v4_waybel_7(X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(superposition,[],[f100,f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(superposition,[],[f102,f106])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_yellow_0)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
      | sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v4_waybel_7(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f28,f39])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r3_orders_2(X0,X3,X1)
                  & r2_hidden(X3,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v4_waybel_7(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r3_orders_2(X0,X3,X1)
                  & r2_hidden(X3,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v4_waybel_7(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X2)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X3,X1)
                            & r2_hidden(X3,X2) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_waybel_7)).

fof(f629,plain,(
    spl12_17 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | spl12_17 ),
    inference(subsumption_resolution,[],[f627,f77])).

fof(f627,plain,
    ( ~ l1_orders_2(sK4)
    | spl12_17 ),
    inference(resolution,[],[f625,f87])).

fof(f87,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f625,plain,
    ( ~ l1_struct_0(sK4)
    | spl12_17 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl12_17
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f626,plain,
    ( spl12_16
    | ~ spl12_17
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f617,f606,f623,f619])).

fof(f617,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_14 ),
    inference(resolution,[],[f608,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f608,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f606])).

fof(f289,plain,
    ( spl12_1
    | ~ spl12_7 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f287,f70])).

fof(f287,plain,
    ( ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f286,f71])).

fof(f286,plain,
    ( ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f285,f72])).

fof(f285,plain,
    ( ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f284,f73])).

fof(f73,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f284,plain,
    ( ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f283,f74])).

fof(f283,plain,
    ( ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f282,f75])).

fof(f282,plain,
    ( ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f281,f76])).

fof(f281,plain,
    ( ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f280,f77])).

fof(f280,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f279,f79])).

fof(f279,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f278,f78])).

fof(f78,plain,(
    v5_waybel_7(k1_waybel_4(sK4),sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f278,plain,
    ( ~ v5_waybel_7(k1_waybel_4(sK4),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f277,f222])).

fof(f222,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f221,f70])).

fof(f221,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f220,f71])).

fof(f220,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f219,f72])).

fof(f219,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f218,f74])).

fof(f218,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f217,f75])).

fof(f217,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f216,f77])).

fof(f216,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f213,f122])).

fof(f122,plain,
    ( ~ v4_waybel_7(sK5,sK4)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f213,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    | v4_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(resolution,[],[f101,f79])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_waybel_7(X1,X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_waybel_7(X1,X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_7)).

fof(f277,plain,
    ( v5_waybel_6(sK5,sK4)
    | ~ v5_waybel_7(k1_waybel_4(sK4),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | spl12_1
    | ~ spl12_7 ),
    inference(resolution,[],[f276,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | v5_waybel_6(X1,X0)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ( sP0(X1,X0,sK9(X0,X1))
            & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( sP0(X1,X0,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sP0(X1,X0,sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( sP0(X1,X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f26,f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,X2,X1)
          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( ~ v5_waybel_6(X1,X0)
              & ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) )
              & v5_waybel_7(k1_waybel_4(X0),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_waybel_7)).

fof(f276,plain,
    ( ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f275,f70])).

fof(f275,plain,
    ( ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f274,f71])).

fof(f274,plain,
    ( ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f273,f72])).

fof(f273,plain,
    ( ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f272,f73])).

fof(f272,plain,
    ( ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f271,f74])).

fof(f271,plain,
    ( ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f270,f75])).

fof(f270,plain,
    ( ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f269,f76])).

fof(f269,plain,
    ( ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f268,f77])).

fof(f268,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f267,f79])).

fof(f267,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f266,f78])).

fof(f266,plain,
    ( ~ v5_waybel_7(k1_waybel_4(sK4),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | spl12_1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f265,f222])).

fof(f265,plain,
    ( v5_waybel_6(sK5,sK4)
    | ~ v5_waybel_7(k1_waybel_4(sK4),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ m1_subset_1(sK9(sK4,sK5),u1_struct_0(sK4))
    | ~ spl12_7 ),
    inference(resolution,[],[f96,f168])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ sP0(sK5,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f167,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X1,sK8(X0,X1,X2),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r3_orders_2(X1,sK8(X0,X1,X2),X0)
        & ~ r3_orders_2(X1,X2,X0)
        & r1_waybel_3(X1,k12_lattice3(X1,X2,sK8(X0,X1,X2)),X0)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X1,X3,X0)
          & ~ r3_orders_2(X1,X2,X0)
          & r1_waybel_3(X1,k12_lattice3(X1,X2,X3),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_orders_2(X1,sK8(X0,X1,X2),X0)
        & ~ r3_orders_2(X1,X2,X0)
        & r1_waybel_3(X1,k12_lattice3(X1,X2,sK8(X0,X1,X2)),X0)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r3_orders_2(X1,X3,X0)
          & ~ r3_orders_2(X1,X2,X0)
          & r1_waybel_3(X1,k12_lattice3(X1,X2,X3),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,X2,X1)
          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ sP0(sK5,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | r3_orders_2(sK4,sK8(sK5,sK4,X0),sK5) )
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f166,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ sP0(sK5,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(sK8(sK5,sK4,X0),u1_struct_0(sK4))
        | r3_orders_2(sK4,sK8(sK5,sK4,X0),sK5) )
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f165,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r3_orders_2(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ sP0(sK5,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(sK8(sK5,sK4,X0),u1_struct_0(sK4))
        | r3_orders_2(sK4,X0,sK5)
        | r3_orders_2(sK4,sK8(sK5,sK4,X0),sK5) )
    | ~ spl12_7 ),
    inference(resolution,[],[f92,f150])).

fof(f150,plain,
    ( ! [X4,X5] :
        ( ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),sK5)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X5,u1_struct_0(sK4))
        | r3_orders_2(sK4,X4,sK5)
        | r3_orders_2(sK4,X5,sK5) )
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl12_7
  <=> ! [X5,X4] :
        ( r3_orders_2(sK4,X5,sK5)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X5,u1_struct_0(sK4))
        | r3_orders_2(sK4,X4,sK5)
        | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X1,k12_lattice3(X1,X2,sK8(X0,X1,X2)),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,sK9(X0,X1))
      | v5_waybel_6(X1,X0)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f151,plain,
    ( spl12_1
    | spl12_7 ),
    inference(avatar_split_clause,[],[f80,f149,f120])).

fof(f80,plain,(
    ! [X4,X5] :
      ( r3_orders_2(sK4,X5,sK5)
      | r3_orders_2(sK4,X4,sK5)
      | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),sK5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | v4_waybel_7(sK5,sK4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f147,plain,
    ( ~ spl12_1
    | spl12_6 ),
    inference(avatar_split_clause,[],[f81,f144,f120])).

fof(f81,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f142,plain,
    ( ~ spl12_1
    | spl12_5 ),
    inference(avatar_split_clause,[],[f82,f139,f120])).

fof(f82,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f137,plain,
    ( ~ spl12_1
    | spl12_4 ),
    inference(avatar_split_clause,[],[f83,f134,f120])).

fof(f83,plain,
    ( r1_waybel_3(sK4,k12_lattice3(sK4,sK6,sK7),sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f132,plain,
    ( ~ spl12_1
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f84,f129,f120])).

fof(f84,plain,
    ( ~ r3_orders_2(sK4,sK6,sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f127,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f85,f124,f120])).

fof(f85,plain,
    ( ~ r3_orders_2(sK4,sK7,sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
