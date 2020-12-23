%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1537+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:48 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  124 (1354 expanded)
%              Number of clauses        :   75 ( 278 expanded)
%              Number of leaves         :   12 ( 418 expanded)
%              Depth                    :   24
%              Number of atoms          :  707 (13484 expanded)
%              Number of equality atoms :  135 ( 595 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( r1_yellow_0(X0,X1)
          <=> ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r1_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r1_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK8,X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK8)
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK7(X2))
        & r2_lattice3(X0,X1,sK7(X2))
        & m1_subset_1(sK7(X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | r1_yellow_0(X0,X1) ) )
     => ( ( ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,sK6,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK6,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,sK6) )
        & ( ? [X4] :
              ( ! [X5] :
                  ( r1_orders_2(X0,X4,X5)
                  | ~ r2_lattice3(X0,sK6,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,sK6,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | r1_yellow_0(X0,sK6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      & r2_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r1_yellow_0(X0,X1) )
            & ( ? [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X4,X5)
                      | ~ r2_lattice3(X0,X1,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r1_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(sK5,X2,X3)
                    & r2_lattice3(sK5,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(sK5)) )
                | ~ r2_lattice3(sK5,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK5)) )
            | ~ r1_yellow_0(sK5,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(sK5,X4,X5)
                    | ~ r2_lattice3(sK5,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK5)) )
                & r2_lattice3(sK5,X1,X4)
                & m1_subset_1(X4,u1_struct_0(sK5)) )
            | r1_yellow_0(sK5,X1) ) )
      & l1_orders_2(sK5)
      & v5_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ! [X2] :
          ( ( ~ r1_orders_2(sK5,X2,sK7(X2))
            & r2_lattice3(sK5,sK6,sK7(X2))
            & m1_subset_1(sK7(X2),u1_struct_0(sK5)) )
          | ~ r2_lattice3(sK5,sK6,X2)
          | ~ m1_subset_1(X2,u1_struct_0(sK5)) )
      | ~ r1_yellow_0(sK5,sK6) )
    & ( ( ! [X5] :
            ( r1_orders_2(sK5,sK8,X5)
            | ~ r2_lattice3(sK5,sK6,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK5)) )
        & r2_lattice3(sK5,sK6,sK8)
        & m1_subset_1(sK8,u1_struct_0(sK5)) )
      | r1_yellow_0(sK5,sK6) )
    & l1_orders_2(sK5)
    & v5_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f25,f29,f28,f27,f26])).

fof(f46,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              & r2_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( sP0(X2,X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f7,f12])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( sP0(X2,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X2,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( sP0(X4,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f19])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP0(sK4(X0,X1),X0,X1)
        & ! [X5] :
            ( r1_orders_2(X0,sK4(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( sP0(sK4(X0,X1),X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,sK4(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK4(X0,X1))
              & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f22,f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X5] :
      ( r1_orders_2(sK5,sK8,X5)
      | ~ r2_lattice3(sK5,sK6,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK5))
      | r1_yellow_0(sK5,sK6) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X2] :
      ( r2_lattice3(sK5,sK6,sK7(X2))
      | ~ r2_lattice3(sK5,sK6,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ r1_yellow_0(sK5,sK6) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK4(X0,X1),X5)
      | ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK5,X2,sK7(X2))
      | ~ r2_lattice3(sK5,sK6,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ r1_yellow_0(sK5,sK6) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK4(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2] :
      ( m1_subset_1(sK7(X2),u1_struct_0(sK5))
      | ~ r2_lattice3(sK5,sK6,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ r1_yellow_0(sK5,sK6) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X3,X4)
                | ~ r2_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X3,X4)
                | ~ r2_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X5,X6)
                & r2_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f14])).

fof(f17,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X5,X6)
          & r2_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X5,sK2(X1,X2,X5))
        & r2_lattice3(X1,X2,sK2(X1,X2,X5))
        & m1_subset_1(sK2(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X3,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK1(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,sK1(X0,X1,X2),X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r2_lattice3(X1,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( sK1(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,sK1(X0,X1,X2),X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,sK1(X0,X1,X2))
          & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,X5,sK2(X1,X2,X5))
              & r2_lattice3(X1,X2,sK2(X1,X2,X5))
              & m1_subset_1(sK2(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f17,f16])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X1,sK1(X0,X1,X2),X4)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_lattice3(X1,X2,sK1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK1(X0,X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,
    ( r2_lattice3(sK5,sK6,sK8)
    | r1_yellow_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5))
    | r1_yellow_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X1 = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_261,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_262,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_266,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X1,X0)
    | ~ r1_orders_2(sK5,X0,X1)
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_262,c_21])).

cnf(c_267,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_4932,plain,
    ( ~ r1_orders_2(sK5,X0,sK8)
    | ~ r1_orders_2(sK5,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X0 = sK8 ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_8628,plain,
    ( ~ r1_orders_2(sK5,sK1(sK8,sK5,sK6),sK8)
    | ~ r1_orders_2(sK5,sK8,sK1(sK8,sK5,sK6))
    | ~ m1_subset_1(sK1(sK8,sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | sK1(sK8,sK5,sK6) = sK8 ),
    inference(instantiation,[status(thm)],[c_4932])).

cnf(c_9,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_348,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_349,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ sP0(X1,sK5,X0)
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_4476,plain,
    ( r2_lattice3(sK5,X0,X1) != iProver_top
    | sP0(X1,sK5,X0) != iProver_top
    | r1_yellow_0(sK5,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_8,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_369,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_370,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r2_lattice3(sK5,X0,sK3(sK5,X0,X1))
    | ~ sP0(X1,sK5,X0)
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_4475,plain,
    ( r2_lattice3(sK5,X0,X1) != iProver_top
    | r2_lattice3(sK5,X0,sK3(sK5,X0,X1)) = iProver_top
    | sP0(X1,sK5,X0) != iProver_top
    | r1_yellow_0(sK5,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_18,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK6,X0)
    | r1_orders_2(sK5,sK8,X0)
    | r1_yellow_0(sK5,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4484,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | r1_orders_2(sK5,sK8,X0) = iProver_top
    | r1_yellow_0(sK5,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5574,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | r1_orders_2(sK5,sK8,sK3(sK5,sK6,X0)) = iProver_top
    | sP0(X0,sK5,sK6) != iProver_top
    | r1_yellow_0(sK5,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,sK6,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4475,c_4484])).

cnf(c_16,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK6,X0)
    | r2_lattice3(sK5,sK6,sK7(X0))
    | ~ r1_yellow_0(sK5,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4486,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | r2_lattice3(sK5,sK6,sK7(X0)) = iProver_top
    | r1_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK4(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_318,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK4(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_319,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r1_orders_2(sK5,sK4(sK5,X0),X1)
    | ~ r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_4478,plain,
    ( r2_lattice3(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK5,sK4(sK5,X0),X1) = iProver_top
    | r1_yellow_0(sK5,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_15,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK6,X0)
    | ~ r1_orders_2(sK5,X0,sK7(X0))
    | ~ r1_yellow_0(sK5,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4487,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | r1_orders_2(sK5,X0,sK7(X0)) != iProver_top
    | r1_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5114,plain,
    ( r2_lattice3(sK5,X0,sK7(sK4(sK5,X0))) != iProver_top
    | r2_lattice3(sK5,sK6,sK4(sK5,X0)) != iProver_top
    | r1_yellow_0(sK5,X0) != iProver_top
    | r1_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7(sK4(sK5,X0)),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4478,c_4487])).

cnf(c_13,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_294,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_295,plain,
    ( ~ r1_yellow_0(sK5,X0)
    | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_296,plain,
    ( r1_yellow_0(sK5,X0) != iProver_top
    | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_5336,plain,
    ( r1_yellow_0(sK5,sK6) != iProver_top
    | r1_yellow_0(sK5,X0) != iProver_top
    | r2_lattice3(sK5,sK6,sK4(sK5,X0)) != iProver_top
    | r2_lattice3(sK5,X0,sK7(sK4(sK5,X0))) != iProver_top
    | m1_subset_1(sK7(sK4(sK5,X0)),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5114,c_296])).

cnf(c_5337,plain,
    ( r2_lattice3(sK5,X0,sK7(sK4(sK5,X0))) != iProver_top
    | r2_lattice3(sK5,sK6,sK4(sK5,X0)) != iProver_top
    | r1_yellow_0(sK5,X0) != iProver_top
    | r1_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(sK7(sK4(sK5,X0)),u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5336])).

cnf(c_5347,plain,
    ( r2_lattice3(sK5,sK6,sK4(sK5,sK6)) != iProver_top
    | r1_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7(sK4(sK5,sK6)),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4486,c_5337])).

cnf(c_4692,plain,
    ( ~ r1_yellow_0(sK5,sK6)
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_4693,plain,
    ( r1_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4692])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,sK4(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_306,plain,
    ( r2_lattice3(X0,X1,sK4(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_307,plain,
    ( r2_lattice3(sK5,X0,sK4(sK5,X0))
    | ~ r1_yellow_0(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_4695,plain,
    ( r2_lattice3(sK5,sK6,sK4(sK5,sK6))
    | ~ r1_yellow_0(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_4696,plain,
    ( r2_lattice3(sK5,sK6,sK4(sK5,sK6)) = iProver_top
    | r1_yellow_0(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4695])).

cnf(c_17,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK6,X0)
    | ~ r1_yellow_0(sK5,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK7(X0),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4772,plain,
    ( ~ r2_lattice3(sK5,sK6,sK4(sK5,sK6))
    | ~ r1_yellow_0(sK5,sK6)
    | ~ m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5))
    | m1_subset_1(sK7(sK4(sK5,sK6)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4776,plain,
    ( r2_lattice3(sK5,sK6,sK4(sK5,sK6)) != iProver_top
    | r1_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7(sK4(sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4772])).

cnf(c_5490,plain,
    ( r1_yellow_0(sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5347,c_4693,c_4696,c_4776])).

cnf(c_5964,plain,
    ( sP0(X0,sK5,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK3(sK5,sK6,X0)) = iProver_top
    | r2_lattice3(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,sK6,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5574,c_4693,c_4696,c_4776,c_5347])).

cnf(c_5965,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | r1_orders_2(sK5,sK8,sK3(sK5,sK6,X0)) = iProver_top
    | sP0(X0,sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,sK6,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5964])).

cnf(c_5975,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | r1_orders_2(sK5,sK8,sK3(sK5,sK6,X0)) = iProver_top
    | sP0(X0,sK5,sK6) != iProver_top
    | r1_yellow_0(sK5,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4476,c_5965])).

cnf(c_6914,plain,
    ( sP0(X0,sK5,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK3(sK5,sK6,X0)) = iProver_top
    | r2_lattice3(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5975,c_4693,c_4696,c_4776,c_5347])).

cnf(c_6915,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | r1_orders_2(sK5,sK8,sK3(sK5,sK6,X0)) = iProver_top
    | sP0(X0,sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6914])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_390,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_391,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,sK3(sK5,X0,X1))
    | ~ sP0(X1,sK5,X0)
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_4474,plain,
    ( r2_lattice3(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK5,X1,sK3(sK5,X0,X1)) != iProver_top
    | sP0(X1,sK5,X0) != iProver_top
    | r1_yellow_0(sK5,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_6924,plain,
    ( r2_lattice3(sK5,sK6,sK8) != iProver_top
    | sP0(sK8,sK5,sK6) != iProver_top
    | r1_yellow_0(sK5,sK6) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6915,c_4474])).

cnf(c_6925,plain,
    ( ~ r2_lattice3(sK5,sK6,sK8)
    | ~ sP0(sK8,sK5,sK6)
    | r1_yellow_0(sK5,sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6924])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK1(X3,X0,X1),X2)
    | sP0(X3,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5080,plain,
    ( ~ r2_lattice3(sK5,sK6,X0)
    | r1_orders_2(sK5,sK1(sK8,sK5,sK6),X0)
    | sP0(sK8,sK5,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6721,plain,
    ( ~ r2_lattice3(sK5,sK6,sK8)
    | r1_orders_2(sK5,sK1(sK8,sK5,sK6),sK8)
    | sP0(sK8,sK5,sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5080])).

cnf(c_6621,plain,
    ( ~ r2_lattice3(sK5,sK6,sK1(sK8,sK5,sK6))
    | r1_orders_2(sK5,sK8,sK1(sK8,sK5,sK6))
    | r1_yellow_0(sK5,sK6)
    | ~ m1_subset_1(sK1(sK8,sK5,sK6),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5492,plain,
    ( ~ r1_yellow_0(sK5,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5490])).

cnf(c_2,plain,
    ( r2_lattice3(X0,X1,sK1(X2,X0,X1))
    | sP0(X2,X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5085,plain,
    ( r2_lattice3(sK5,sK6,sK1(sK8,sK5,sK6))
    | sP0(sK8,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( sP0(X0,X1,X2)
    | sK1(X0,X1,X2) != X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5074,plain,
    ( sP0(sK8,sK5,sK6)
    | sK1(sK8,sK5,sK6) != sK8 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5078,plain,
    ( sK1(sK8,sK5,sK6) != sK8
    | sP0(sK8,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5074])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5075,plain,
    ( sP0(sK8,sK5,sK6)
    | m1_subset_1(sK1(sK8,sK5,sK6),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_19,negated_conjecture,
    ( r2_lattice3(sK5,sK6,sK8)
    | r1_yellow_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,plain,
    ( r2_lattice3(sK5,sK6,sK8) = iProver_top
    | r1_yellow_0(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( r1_yellow_0(sK5,sK6)
    | m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,plain,
    ( r1_yellow_0(sK5,sK6) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8628,c_6925,c_6924,c_6721,c_6621,c_5492,c_5490,c_5085,c_5078,c_5075,c_26,c_19,c_25,c_20])).


%------------------------------------------------------------------------------
