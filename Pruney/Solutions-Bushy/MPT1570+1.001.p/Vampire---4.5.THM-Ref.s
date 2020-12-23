%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1570+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:07 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  204 (56047 expanded)
%              Number of leaves         :   10 (21305 expanded)
%              Depth                    :   93
%              Number of atoms          : 1143 (584012 expanded)
%              Number of equality atoms :   59 (30616 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f562,plain,(
    $false ),
    inference(subsumption_resolution,[],[f554,f29])).

fof(f29,plain,(
    ~ r2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    & r2_yellow_0(sK2,sK3)
    & ! [X3] :
        ( ( ( r1_lattice3(sK2,sK3,X3)
            | ~ r1_lattice3(sK2,sK4,X3) )
          & ( r1_lattice3(sK2,sK4,X3)
            | ~ r1_lattice3(sK2,sK3,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & ! [X3] :
                ( ( ( r1_lattice3(X0,X1,X3)
                    | ~ r1_lattice3(X0,X2,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                    | ~ r1_lattice3(X0,X1,X3) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ~ r2_yellow_0(sK2,X2)
          & r2_yellow_0(sK2,X1)
          & ! [X3] :
              ( ( ( r1_lattice3(sK2,X1,X3)
                  | ~ r1_lattice3(sK2,X2,X3) )
                & ( r1_lattice3(sK2,X2,X3)
                  | ~ r1_lattice3(sK2,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2,X1] :
        ( ~ r2_yellow_0(sK2,X2)
        & r2_yellow_0(sK2,X1)
        & ! [X3] :
            ( ( ( r1_lattice3(sK2,X1,X3)
                | ~ r1_lattice3(sK2,X2,X3) )
              & ( r1_lattice3(sK2,X2,X3)
                | ~ r1_lattice3(sK2,X1,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) )
   => ( ~ r2_yellow_0(sK2,sK4)
      & r2_yellow_0(sK2,sK3)
      & ! [X3] :
          ( ( ( r1_lattice3(sK2,sK3,X3)
              | ~ r1_lattice3(sK2,sK4,X3) )
            & ( r1_lattice3(sK2,sK4,X3)
              | ~ r1_lattice3(sK2,sK3,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X2,X3)
                  | ~ r1_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( r2_yellow_0(X0,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                  <=> r1_lattice3(X0,X2,X3) ) ) )
           => r2_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f2])).

% (10608)Refutation not found, incomplete strategy% (10608)------------------------------
% (10608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10608)Termination reason: Refutation not found, incomplete strategy

% (10608)Memory used [KB]: 10490
% (10608)Time elapsed: 0.073 s
% (10608)------------------------------
% (10608)------------------------------
fof(f2,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_yellow_0)).

fof(f554,plain,(
    r2_yellow_0(sK2,sK4) ),
    inference(resolution,[],[f548,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ sP0(sK2,X0)
      | r2_yellow_0(sK2,X0) ) ),
    inference(resolution,[],[f51,f25])).

fof(f25,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f10,f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ? [X2] :
          ( ! [X3] :
              ( X2 = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_lattice3(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & ! [X5] :
              ( r1_orders_2(X0,X5,X2)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_0)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f548,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f547,f288])).

fof(f288,plain,
    ( m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f287,f25])).

fof(f287,plain,
    ( sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f286,f50])).

fof(f286,plain,
    ( ~ sP1(sK2)
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f285,f28])).

fof(f28,plain,(
    r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f285,plain,
    ( m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ r2_yellow_0(sK2,sK3)
    | ~ sP1(sK2) ),
    inference(resolution,[],[f284,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r2_yellow_0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f284,plain,
    ( ~ sP0(sK2,sK3)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f283,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ( sK5(X0,X1,X2) != X2
              & ! [X4] :
                  ( r1_orders_2(X0,X4,sK5(X0,X1,X2))
                  | ~ r1_lattice3(X0,X1,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK5(X0,X1,X2))
              & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
            | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
              & r1_lattice3(X0,X1,sK6(X0,X1,X2))
              & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ( ! [X7] :
              ( sK7(X0,X1) = X7
              | ( ~ r1_orders_2(X0,sK8(X0,X1,X7),X7)
                & r1_lattice3(X0,X1,sK8(X0,X1,X7))
                & m1_subset_1(sK8(X0,X1,X7),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X9,sK7(X0,X1))
              | ~ r1_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,sK7(X0,X1))
          & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f18,f22,f21,f20,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK5(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,X4,sK5(X0,X1,X2))
            | ~ r1_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X5,X2)
          & r1_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( X6 = X7
              | ? [X8] :
                  ( ~ r1_orders_2(X0,X8,X7)
                  & r1_lattice3(X0,X1,X8)
                  & m1_subset_1(X8,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X9,X6)
              | ~ r1_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ! [X7] :
            ( sK7(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X8,X7)
                & r1_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,X9,sK7(X0,X1))
            | ~ r1_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK7(X0,X1))
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X8,X7)
          & r1_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK8(X0,X1,X7),X7)
        & r1_lattice3(X0,X1,sK8(X0,X1,X7))
        & m1_subset_1(sK8(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ? [X3] :
                ( X2 != X3
                & ! [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ? [X5] :
                ( ~ r1_orders_2(X0,X5,X2)
                & r1_lattice3(X0,X1,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X6] :
            ( ! [X7] :
                ( X6 = X7
                | ? [X8] :
                    ( ~ r1_orders_2(X0,X8,X7)
                    & r1_lattice3(X0,X1,X8)
                    & m1_subset_1(X8,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X7)
                | ~ m1_subset_1(X7,u1_struct_0(X0)) )
            & ! [X9] :
                ( r1_orders_2(X0,X9,X6)
                | ~ r1_lattice3(X0,X1,X9)
                | ~ m1_subset_1(X9,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X6)
            & m1_subset_1(X6,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ? [X3] :
                ( X2 != X3
                & ! [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ? [X5] :
                ( ~ r1_orders_2(X0,X5,X2)
                & r1_lattice3(X0,X1,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( ! [X3] :
                ( X2 = X3
                | ? [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    & r1_lattice3(X0,X1,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & ! [X5] :
                ( r1_orders_2(X0,X5,X2)
                | ~ r1_lattice3(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f283,plain,
    ( sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f282,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f282,plain,
    ( ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f280,f26])).

fof(f26,plain,(
    ! [X3] :
      ( r1_lattice3(sK2,sK4,X3)
      | ~ r1_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f280,plain,
    ( ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f279,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) != X2
      | sP0(X0,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f279,plain,
    ( sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f277,f124])).

fof(f124,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( sP0(sK2,sK4)
    | r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f119,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | sP0(X0,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f119,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))) ),
    inference(resolution,[],[f118,f27])).

fof(f27,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X3)
      | r1_lattice3(sK2,sK3,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,
    ( m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f117,f25])).

fof(f117,plain,
    ( sP0(sK2,sK4)
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f116,f50])).

fof(f116,plain,
    ( ~ sP1(sK2)
    | sP0(sK2,sK4)
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f115,f28])).

fof(f115,plain,
    ( m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ r2_yellow_0(sK2,sK3)
    | ~ sP1(sK2) ),
    inference(resolution,[],[f114,f30])).

fof(f114,plain,
    ( ~ sP0(sK2,sK3)
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f113,f32])).

fof(f113,plain,
    ( sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f112,f33])).

fof(f112,plain,
    ( ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f110,f26])).

fof(f110,plain,
    ( ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( sP0(sK2,sK4)
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4) ),
    inference(resolution,[],[f108,f76])).

fof(f76,plain,(
    ! [X3] :
      ( r1_lattice3(sK2,sK3,sK6(sK2,sK4,X3))
      | ~ r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | m1_subset_1(sK5(sK2,sK4,X3),u1_struct_0(sK2))
      | sP0(sK2,sK4) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X3] :
      ( sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | m1_subset_1(sK5(sK2,sK4,X3),u1_struct_0(sK2))
      | r1_lattice3(sK2,sK3,sK6(sK2,sK4,X3))
      | m1_subset_1(sK5(sK2,sK4,X3),u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,sK4,sK6(sK2,X0,X1))
      | sP0(sK2,X0)
      | ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | m1_subset_1(sK5(sK2,X0,X1),u1_struct_0(sK2))
      | r1_lattice3(sK2,sK3,sK6(sK2,X0,X1)) ) ),
    inference(resolution,[],[f38,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,
    ( ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f107,f25])).

fof(f107,plain,
    ( m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f106,f50])).

fof(f106,plain,
    ( ~ sP1(sK2)
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f105,f28])).

fof(f105,plain,
    ( ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ r2_yellow_0(sK2,sK3)
    | ~ sP1(sK2) ),
    inference(resolution,[],[f104,f30])).

fof(f104,plain,
    ( ~ sP0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f103,f32])).

fof(f103,plain,
    ( sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f101,f33])).

fof(f101,plain,
    ( ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f100,f26])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,X0,sK7(sK2,sK3))
      | m1_subset_1(sK5(sK2,X0,sK7(sK2,sK3)),u1_struct_0(sK2))
      | sP0(sK2,X0)
      | ~ r1_lattice3(sK2,sK3,sK6(sK2,X0,sK7(sK2,sK3))) ) ),
    inference(resolution,[],[f99,f28])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK2,X1)
      | sP0(sK2,X0)
      | m1_subset_1(sK5(sK2,X0,sK7(sK2,X1)),u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X1))
      | ~ r1_lattice3(sK2,X1,sK6(sK2,X0,sK7(sK2,X1))) ) ),
    inference(resolution,[],[f98,f25])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X2,sK7(X0,X1)),u1_struct_0(X0))
      | sP0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X2,sK7(X0,X1))
      | ~ r1_lattice3(X0,X1,sK6(X0,X2,sK7(X0,X1))) ) ),
    inference(resolution,[],[f97,f50])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0)
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,sK7(X0,X2)))
      | m1_subset_1(sK5(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2)) ) ),
    inference(resolution,[],[f96,f30])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2))
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,sK7(X0,X2)))
      | m1_subset_1(sK5(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f95,f32])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2))
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,sK7(X0,X2)))
      | m1_subset_1(sK5(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | ~ sP0(X0,X2)
      | ~ m1_subset_1(sK7(X0,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2))
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,sK7(X0,X2)))
      | m1_subset_1(sK5(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | ~ sP0(X0,X2)
      | m1_subset_1(sK5(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2))
      | ~ m1_subset_1(sK7(X0,X2),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f64,f38])).

% (10615)Refutation not found, incomplete strategy% (10615)------------------------------
% (10615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2))
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,sK7(X0,X2)))
      | m1_subset_1(sK5(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | ~ sP0(X0,X2) ) ),
    inference(subsumption_resolution,[],[f63,f32])).

% (10615)Termination reason: Refutation not found, incomplete strategy

% (10615)Memory used [KB]: 1663
% (10615)Time elapsed: 0.064 s
% (10615)------------------------------
% (10615)------------------------------
fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2))
      | ~ m1_subset_1(sK7(X0,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,sK7(X0,X2)))
      | ~ m1_subset_1(sK6(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | ~ sP0(X0,X2) ) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1,X9] :
      ( r1_orders_2(X0,X9,sK7(X0,X1))
      | ~ r1_lattice3(X0,X1,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f277,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f276,f25])).

fof(f276,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f275,f50])).

fof(f275,plain,
    ( ~ sP1(sK2)
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f274,f28])).

fof(f274,plain,
    ( sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ sP1(sK2) ),
    inference(resolution,[],[f273,f30])).

fof(f273,plain,
    ( ~ sP0(sK2,sK3)
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f272,f118])).

fof(f272,plain,
    ( m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f271,f35])).

fof(f35,plain,(
    ! [X0,X7,X1] :
      ( m1_subset_1(sK8(X0,X1,X7),u1_struct_0(X0))
      | sK7(X0,X1) = X7
      | ~ r1_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f271,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f267,f36])).

fof(f36,plain,(
    ! [X0,X7,X1] :
      ( r1_lattice3(X0,X1,sK8(X0,X1,X7))
      | sK7(X0,X1) = X7
      | ~ r1_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f267,plain,
    ( ~ r1_lattice3(sK2,sK3,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,
    ( sP0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ r1_lattice3(sK2,sK3,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2)) ),
    inference(resolution,[],[f147,f26])).

fof(f147,plain,
    ( ~ r1_lattice3(sK2,sK4,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f143,f118])).

fof(f143,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))) ),
    inference(resolution,[],[f142,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK8(sK2,sK3,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sK7(sK2,sK3) = X0
      | ~ r1_lattice3(sK2,sK3,X0) ) ),
    inference(resolution,[],[f68,f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK2,X1)
      | sK7(sK2,X1) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,sK8(sK2,X1,X0),X0)
      | ~ r1_lattice3(sK2,X1,X0) ) ),
    inference(resolution,[],[f67,f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sK7(X0,X1) = X2
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f61,f50])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sK7(X0,X1) = X2
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK8(X0,X1,X2),X2) ) ),
    inference(resolution,[],[f37,f30])).

fof(f37,plain,(
    ! [X0,X7,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_orders_2(X0,sK8(X0,X1,X7),X7)
      | ~ r1_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | sK7(X0,X1) = X7 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f142,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X0)
      | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f141,f25])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f140,f50])).

fof(f140,plain,(
    ! [X0] :
      ( ~ sP1(sK2)
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f139,f28])).

fof(f139,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | ~ r2_yellow_0(sK2,sK3)
      | ~ sP1(sK2) ) ),
    inference(resolution,[],[f138,f30])).

fof(f138,plain,(
    ! [X0] :
      ( ~ sP0(sK2,sK3)
      | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f137,f32])).

fof(f137,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
      | ~ sP0(sK2,sK3) ) ),
    inference(resolution,[],[f131,f33])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f130,f26])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,sK7(sK2,sK3))
      | sP0(sK2,X0)
      | r1_orders_2(sK2,X1,sK5(sK2,X0,sK7(sK2,sK3)))
      | m1_subset_1(sK6(sK2,X0,sK7(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f129,f28])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(sK2,X1)
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X1))
      | sP0(sK2,X0)
      | r1_orders_2(sK2,X2,sK5(sK2,X0,sK7(sK2,X1)))
      | m1_subset_1(sK6(sK2,X0,sK7(sK2,X1)),u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f127,f25])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X1)
      | m1_subset_1(sK6(X1,X2,sK7(X1,X3)),u1_struct_0(X1))
      | ~ r1_lattice3(X1,X2,sK7(X1,X3))
      | sP0(X1,X2)
      | r1_orders_2(X1,X0,sK5(X1,X2,sK7(X1,X3)))
      | ~ r2_yellow_0(X1,X3)
      | ~ r1_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f92,f50])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,sK7(X0,X3)),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,sK7(X0,X3))
      | sP0(X0,X1)
      | r1_orders_2(X0,X2,sK5(X0,X1,sK7(X0,X3)))
      | ~ r2_yellow_0(X0,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f82,f30])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X3)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X2,sK7(X0,X3)),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,sK7(X0,X3))
      | sP0(X0,X2)
      | r1_orders_2(X0,X1,sK5(X0,X2,sK7(X0,X3))) ) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,sK5(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f547,plain,
    ( sP0(sK2,sK4)
    | ~ m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f546,f513])).

fof(f513,plain,
    ( r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f512,f463])).

fof(f463,plain,
    ( m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | sP0(sK2,sK4) ),
    inference(superposition,[],[f118,f455])).

fof(f455,plain,(
    sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f447,f29])).

fof(f447,plain,
    ( sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | r2_yellow_0(sK2,sK4) ),
    inference(resolution,[],[f444,f52])).

fof(f444,plain,
    ( sP0(sK2,sK4)
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f443,f25])).

fof(f443,plain,
    ( sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f442,f50])).

fof(f442,plain,
    ( ~ sP1(sK2)
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f441,f28])).

fof(f441,plain,
    ( sP0(sK2,sK4)
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ sP1(sK2) ),
    inference(resolution,[],[f440,f30])).

fof(f440,plain,
    ( ~ sP0(sK2,sK3)
    | sP0(sK2,sK4)
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f439,f118])).

fof(f439,plain,
    ( sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f438,f319])).

fof(f319,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( sP0(sK2,sK4)
    | sP0(sK2,sK4)
    | r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))) ),
    inference(resolution,[],[f312,f119])).

fof(f312,plain,
    ( r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f311,f25])).

fof(f311,plain,
    ( sP0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f310,f50])).

fof(f310,plain,
    ( ~ sP1(sK2)
    | sP0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f309,f28])).

fof(f309,plain,
    ( r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ r2_yellow_0(sK2,sK3)
    | ~ sP1(sK2) ),
    inference(resolution,[],[f308,f30])).

fof(f308,plain,
    ( ~ sP0(sK2,sK3)
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f307,f32])).

fof(f307,plain,
    ( sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f306,f33])).

fof(f306,plain,
    ( ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3))) ),
    inference(duplicate_literal_removal,[],[f305])).

fof(f305,plain,
    ( r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f304,f26])).

fof(f304,plain,
    ( ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f298,f302])).

fof(f302,plain,
    ( ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f301,f25])).

fof(f301,plain,
    ( ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f300,f50])).

fof(f300,plain,
    ( ~ sP1(sK2)
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f299,f28])).

fof(f299,plain,
    ( ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ r2_yellow_0(sK2,sK3)
    | ~ sP1(sK2) ),
    inference(resolution,[],[f293,f30])).

fof(f293,plain,
    ( ~ sP0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,
    ( sP0(sK2,sK4)
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f288,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2))
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,sK7(X0,X2)))
      | r1_lattice3(X0,X1,sK5(X0,X1,sK7(X0,X2)))
      | ~ sP0(X0,X2) ) ),
    inference(subsumption_resolution,[],[f65,f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,sK7(X0,X2)))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK7(X0,X2))
      | ~ m1_subset_1(sK7(X0,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,sK6(X0,X1,sK7(X0,X2)))
      | ~ m1_subset_1(sK6(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | ~ sP0(X0,X2) ) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f298,plain,
    ( sP0(sK2,sK4)
    | r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,
    ( sP0(sK2,sK4)
    | r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
    | r1_lattice3(sK2,sK4,sK5(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f290,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f290,plain,
    ( ~ r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
    | sP0(sK2,sK4)
    | r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3))) ),
    inference(resolution,[],[f288,f27])).

fof(f438,plain,
    ( sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f437,f35])).

fof(f437,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f436])).

fof(f436,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4)
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3)))
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f435,f36])).

fof(f435,plain,
    ( ~ r1_lattice3(sK2,sK3,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f434])).

fof(f434,plain,
    ( sP0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2)) ),
    inference(resolution,[],[f427,f26])).

fof(f427,plain,
    ( ~ r1_lattice3(sK2,sK4,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f426,f319])).

fof(f426,plain,
    ( sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f422,f118])).

fof(f422,plain,
    ( sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))))
    | ~ m1_subset_1(sK8(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2))
    | sK7(sK2,sK3) = sK5(sK2,sK4,sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK4,sK7(sK2,sK3))) ),
    inference(resolution,[],[f421,f69])).

fof(f421,plain,(
    ! [X2] :
      ( r1_orders_2(sK2,X2,sK5(sK2,sK4,sK7(sK2,sK3)))
      | sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(global_subsumption,[],[f159,f183,f290])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X0)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | sP0(sK2,sK4) ) ),
    inference(subsumption_resolution,[],[f182,f25])).

fof(f182,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | sP0(sK2,sK4)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f181,f50])).

fof(f181,plain,(
    ! [X0] :
      ( ~ sP1(sK2)
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | sP0(sK2,sK4) ) ),
    inference(subsumption_resolution,[],[f180,f28])).

fof(f180,plain,(
    ! [X0] :
      ( sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | ~ r2_yellow_0(sK2,sK3)
      | ~ sP1(sK2) ) ),
    inference(resolution,[],[f179,f30])).

fof(f179,plain,(
    ! [X0] :
      ( ~ sP0(sK2,sK3)
      | sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f178,f32])).

fof(f178,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
      | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
      | ~ sP0(sK2,sK3) ) ),
    inference(resolution,[],[f176,f33])).

fof(f176,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK3,sK6(sK2,sK4,sK7(sK2,sK3)))
      | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f175,f26])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,sK7(sK2,sK3))
      | ~ r1_lattice3(sK2,sK3,sK6(sK2,X0,sK7(sK2,sK3)))
      | r1_orders_2(sK2,X1,sK5(sK2,X0,sK7(sK2,sK3)))
      | sP0(sK2,X0)
      | ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f174,f28])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(sK2,X1)
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X1))
      | ~ r1_lattice3(sK2,X1,sK6(sK2,X0,sK7(sK2,X1)))
      | r1_orders_2(sK2,X2,sK5(sK2,X0,sK7(sK2,X1)))
      | sP0(sK2,X0)
      | ~ r1_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f173,f25])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X1)
      | sP0(X1,X2)
      | ~ r1_lattice3(X1,X2,sK7(X1,X3))
      | ~ r1_lattice3(X1,X3,sK6(X1,X2,sK7(X1,X3)))
      | r1_orders_2(X1,X0,sK5(X1,X2,sK7(X1,X3)))
      | ~ r2_yellow_0(X1,X3)
      | ~ r1_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f172,f50])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK7(X0,X3))
      | ~ r1_lattice3(X0,X3,sK6(X0,X1,sK7(X0,X3)))
      | r1_orders_2(X0,X2,sK5(X0,X1,sK7(X0,X3)))
      | ~ r2_yellow_0(X0,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f171,f30])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X3)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK7(X0,X3))
      | ~ r1_lattice3(X0,X3,sK6(X0,X2,sK7(X0,X3)))
      | r1_orders_2(X0,X1,sK5(X0,X2,sK7(X0,X3))) ) ),
    inference(subsumption_resolution,[],[f89,f82])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK5(X0,X2,sK7(X0,X3)))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK7(X0,X3))
      | ~ r1_lattice3(X0,X3,sK6(X0,X2,sK7(X0,X3)))
      | ~ m1_subset_1(sK6(X0,X2,sK7(X0,X3)),u1_struct_0(X0))
      | ~ sP0(X0,X3) ) ),
    inference(subsumption_resolution,[],[f88,f32])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK5(X0,X2,sK7(X0,X3)))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK7(X0,X3))
      | ~ m1_subset_1(sK7(X0,X3),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X3,sK6(X0,X2,sK7(X0,X3)))
      | ~ m1_subset_1(sK6(X0,X2,sK7(X0,X3)),u1_struct_0(X0))
      | ~ sP0(X0,X3) ) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r1_orders_2(X0,X4,sK5(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f159,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X0)
      | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f158,f25])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f157,f50])).

fof(f157,plain,(
    ! [X0] :
      ( ~ sP1(sK2)
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f156,f28])).

fof(f156,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | ~ r2_yellow_0(sK2,sK3)
      | ~ sP1(sK2) ) ),
    inference(resolution,[],[f155,f30])).

fof(f155,plain,(
    ! [X0] :
      ( ~ sP0(sK2,sK3)
      | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f154,f32])).

fof(f154,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
      | ~ sP0(sK2,sK3) ) ),
    inference(resolution,[],[f135,f33])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3))
      | r1_orders_2(sK2,X0,sK5(sK2,sK4,sK7(sK2,sK3)))
      | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(sK2,sK4)
      | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f134,f26])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,sK7(sK2,sK3))
      | sP0(sK2,X0)
      | r1_orders_2(sK2,X1,sK5(sK2,X0,sK7(sK2,sK3)))
      | r1_lattice3(sK2,X0,sK6(sK2,X0,sK7(sK2,sK3)))
      | ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f133,f28])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(sK2,X1)
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X1))
      | sP0(sK2,X0)
      | r1_orders_2(sK2,X2,sK5(sK2,X0,sK7(sK2,X1)))
      | r1_lattice3(sK2,X0,sK6(sK2,X0,sK7(sK2,X1)))
      | ~ r1_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f128,f25])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X1)
      | r1_lattice3(X1,X2,sK6(X1,X2,sK7(X1,X3)))
      | ~ r1_lattice3(X1,X2,sK7(X1,X3))
      | sP0(X1,X2)
      | r1_orders_2(X1,X0,sK5(X1,X2,sK7(X1,X3)))
      | ~ r2_yellow_0(X1,X3)
      | ~ r1_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f93,f50])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK6(X0,X1,sK7(X0,X3)))
      | ~ r1_lattice3(X0,X1,sK7(X0,X3))
      | sP0(X0,X1)
      | r1_orders_2(X0,X2,sK5(X0,X1,sK7(X0,X3)))
      | ~ r2_yellow_0(X0,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f85,f30])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X3)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattice3(X0,X2,sK6(X0,X2,sK7(X0,X3)))
      | ~ r1_lattice3(X0,X2,sK7(X0,X3))
      | sP0(X0,X2)
      | r1_orders_2(X0,X1,sK5(X0,X2,sK7(X0,X3))) ) ),
    inference(resolution,[],[f45,f32])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,sK5(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f512,plain,
    ( sP0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f483,f469])).

fof(f469,plain,
    ( r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | sP0(sK2,sK4) ),
    inference(superposition,[],[f312,f455])).

fof(f483,plain,
    ( sP0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(trivial_inequality_removal,[],[f480])).

fof(f480,plain,
    ( sK7(sK2,sK3) != sK7(sK2,sK3)
    | sP0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(superposition,[],[f48,f455])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) != X2
      | sP0(X0,X1)
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f546,plain,
    ( sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
    | ~ m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f544])).

fof(f544,plain,
    ( sP0(sK2,sK4)
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK6(sK2,sK4,sK7(sK2,sK3)))
    | ~ m1_subset_1(sK6(sK2,sK4,sK7(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f543,f477])).

fof(f477,plain,(
    ! [X10] :
      ( r1_orders_2(sK2,X10,sK7(sK2,sK3))
      | sP0(sK2,sK4)
      | ~ r1_lattice3(sK2,sK4,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK2)) ) ),
    inference(superposition,[],[f421,f455])).

fof(f543,plain,
    ( ~ r1_orders_2(sK2,sK6(sK2,sK4,sK7(sK2,sK3)),sK7(sK2,sK3))
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f542,f463])).

fof(f542,plain,
    ( sP0(sK2,sK4)
    | ~ r1_orders_2(sK2,sK6(sK2,sK4,sK7(sK2,sK3)),sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f484,f469])).

fof(f484,plain,
    ( sP0(sK2,sK4)
    | ~ r1_orders_2(sK2,sK6(sK2,sK4,sK7(sK2,sK3)),sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(trivial_inequality_removal,[],[f479])).

fof(f479,plain,
    ( sK7(sK2,sK3) != sK7(sK2,sK3)
    | sP0(sK2,sK4)
    | ~ r1_orders_2(sK2,sK6(sK2,sK4,sK7(sK2,sK3)),sK7(sK2,sK3))
    | ~ r1_lattice3(sK2,sK4,sK7(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2)) ),
    inference(superposition,[],[f49,f455])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) != X2
      | sP0(X0,X1)
      | ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
