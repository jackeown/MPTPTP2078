%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1570+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:55 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  143 (1053 expanded)
%              Number of clauses        :   99 ( 244 expanded)
%              Number of leaves         :    9 ( 264 expanded)
%              Depth                    :   32
%              Number of atoms          :  737 (8411 expanded)
%              Number of equality atoms :  268 ( 649 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f6,plain,(
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
    inference(flattening,[],[f6])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              & r1_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( sP0(X2,X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f7,f10])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( sP0(X2,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X5,X2)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( sP0(X4,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f17])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP0(sK4(X0,X1),X0,X1)
        & ! [X5] :
            ( r1_orders_2(X0,X5,sK4(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( sP0(sK4(X0,X1),X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X5,sK4(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK4(X0,X1))
              & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f20,f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP0(sK4(X0,X1),X0,X1)
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f5,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( ( r2_yellow_0(X0,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                  <=> r1_lattice3(X0,X2,X3) ) ) )
           => r2_yellow_0(X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f22,plain,(
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
      & l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X2,X3)
                  | ~ r1_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
     => ( ~ r2_yellow_0(X0,sK7)
        & r2_yellow_0(X0,sK6)
        & ! [X3] :
            ( ( ( r1_lattice3(X0,sK6,X3)
                | ~ r1_lattice3(X0,sK7,X3) )
              & ( r1_lattice3(X0,sK7,X3)
                | ~ r1_lattice3(X0,sK6,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
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
        & l1_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ~ r2_yellow_0(sK5,X2)
          & r2_yellow_0(sK5,X1)
          & ! [X3] :
              ( ( ( r1_lattice3(sK5,X1,X3)
                  | ~ r1_lattice3(sK5,X2,X3) )
                & ( r1_lattice3(sK5,X2,X3)
                  | ~ r1_lattice3(sK5,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) )
      & l1_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r2_yellow_0(sK5,sK7)
    & r2_yellow_0(sK5,sK6)
    & ! [X3] :
        ( ( ( r1_lattice3(sK5,sK6,X3)
            | ~ r1_lattice3(sK5,sK7,X3) )
          & ( r1_lattice3(sK5,sK7,X3)
            | ~ r1_lattice3(sK5,sK6,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
    & l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f24,f23])).

fof(f40,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X4,X3)
                | ~ r1_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X4,X3)
                | ~ r1_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X6,X5)
                & r1_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f12])).

fof(f15,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X6,X5)
          & r1_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK2(X1,X2,X5),X5)
        & r1_lattice3(X1,X2,sK2(X1,X2,X5))
        & m1_subset_1(sK2(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X4,X3)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK1(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,X4,sK1(X0,X1,X2))
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r1_lattice3(X1,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( sK1(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,X4,sK1(X0,X1,X2))
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,sK1(X0,X1,X2))
          & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,sK2(X1,X2,X5),X5)
              & r1_lattice3(X1,X2,sK2(X1,X2,X5))
              & m1_subset_1(sK2(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f15,f14])).

fof(f26,plain,(
    ! [X2,X0,X5,X1] :
      ( X0 = X5
      | m1_subset_1(sK2(X1,X2,X5),u1_struct_0(X1))
      | ~ r1_lattice3(X1,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X2,X0,X5,X1] :
      ( X0 = X5
      | r1_lattice3(X1,X2,sK2(X1,X2,X5))
      | ~ r1_lattice3(X1,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X3] :
      ( r1_lattice3(sK5,sK7,X3)
      | ~ r1_lattice3(sK5,sK6,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    r2_yellow_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X1,X4,sK1(X0,X1,X2))
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X5,X1] :
      ( X0 = X5
      | ~ r1_orders_2(X1,sK2(X1,X2,X5),X5)
      | ~ r1_lattice3(X1,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_lattice3(X1,X2,sK1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X3] :
      ( r1_lattice3(sK5,sK6,X3)
      | ~ r1_lattice3(sK5,sK7,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ~ r2_yellow_0(sK5,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK4(X0,X1))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK1(X0,X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_10,plain,
    ( sP0(sK4(X0,X1),X0,X1)
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_258,plain,
    ( sP0(sK4(X0,X1),X0,X1)
    | ~ r2_yellow_0(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_259,plain,
    ( sP0(sK4(sK5,X0),sK5,X0)
    | ~ r2_yellow_0(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_3401,plain,
    ( sP0(sK4(sK5,X0),sK5,X0) = iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_6,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ sP0(X3,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3409,plain,
    ( X0 = X1
    | r1_lattice3(X2,X3,X0) != iProver_top
    | sP0(X1,X2,X3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK2(X2,X3,X0),u1_struct_0(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4370,plain,
    ( sK4(sK5,X0) = X1
    | r1_lattice3(sK5,X0,X1) != iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_3409])).

cnf(c_5,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK2(X0,X1,X2))
    | ~ sP0(X3,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3410,plain,
    ( X0 = X1
    | r1_lattice3(X2,X3,X0) != iProver_top
    | r1_lattice3(X2,X3,sK2(X2,X3,X0)) = iProver_top
    | sP0(X1,X2,X3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4492,plain,
    ( sK4(sK5,X0) = X1
    | r1_lattice3(sK5,X0,X1) != iProver_top
    | r1_lattice3(sK5,X0,sK2(sK5,X0,X1)) = iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_3410])).

cnf(c_17,negated_conjecture,
    ( ~ r1_lattice3(sK5,sK6,X0)
    | r1_lattice3(sK5,sK7,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3405,plain,
    ( r1_lattice3(sK5,sK6,X0) != iProver_top
    | r1_lattice3(sK5,sK7,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4966,plain,
    ( sK4(sK5,sK6) = X0
    | r1_lattice3(sK5,sK6,X0) != iProver_top
    | r1_lattice3(sK5,sK7,sK2(sK5,sK6,X0)) = iProver_top
    | r2_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4492,c_3405])).

cnf(c_15,negated_conjecture,
    ( r2_yellow_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_26,plain,
    ( r2_yellow_0(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4985,plain,
    ( r1_lattice3(sK5,sK7,sK2(sK5,sK6,X0)) = iProver_top
    | r1_lattice3(sK5,sK6,X0) != iProver_top
    | sK4(sK5,sK6) = X0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4966,c_26])).

cnf(c_4986,plain,
    ( sK4(sK5,sK6) = X0
    | r1_lattice3(sK5,sK6,X0) != iProver_top
    | r1_lattice3(sK5,sK7,sK2(sK5,sK6,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4985])).

cnf(c_4996,plain,
    ( sK4(sK5,sK6) = X0
    | r1_lattice3(sK5,sK6,X0) != iProver_top
    | r1_lattice3(sK5,sK7,sK2(sK5,sK6,X0)) = iProver_top
    | r2_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4370,c_4986])).

cnf(c_5023,plain,
    ( r1_lattice3(sK5,sK7,sK2(sK5,sK6,X0)) = iProver_top
    | r1_lattice3(sK5,sK6,X0) != iProver_top
    | sK4(sK5,sK6) = X0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4996,c_26])).

cnf(c_5024,plain,
    ( sK4(sK5,sK6) = X0
    | r1_lattice3(sK5,sK6,X0) != iProver_top
    | r1_lattice3(sK5,sK7,sK2(sK5,sK6,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5023])).

cnf(c_1,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK1(X3,X0,X1))
    | sP0(X3,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3414,plain,
    ( r1_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X2,sK1(X3,X0,X1)) = iProver_top
    | sP0(X3,X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | ~ sP0(X3,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3411,plain,
    ( X0 = X1
    | r1_lattice3(X2,X3,X0) != iProver_top
    | r1_orders_2(X2,sK2(X2,X3,X0),X0) != iProver_top
    | sP0(X1,X2,X3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4500,plain,
    ( sK1(X0,X1,X2) = X3
    | r1_lattice3(X1,X2,sK2(X1,X4,sK1(X0,X1,X2))) != iProver_top
    | r1_lattice3(X1,X4,sK1(X0,X1,X2)) != iProver_top
    | sP0(X3,X1,X4) != iProver_top
    | sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK2(X1,X4,sK1(X0,X1,X2)),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3414,c_3411])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_58,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5250,plain,
    ( m1_subset_1(sK2(X1,X4,sK1(X0,X1,X2)),u1_struct_0(X1)) != iProver_top
    | sP0(X0,X1,X2) = iProver_top
    | sP0(X3,X1,X4) != iProver_top
    | r1_lattice3(X1,X4,sK1(X0,X1,X2)) != iProver_top
    | r1_lattice3(X1,X2,sK2(X1,X4,sK1(X0,X1,X2))) != iProver_top
    | sK1(X0,X1,X2) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4500,c_58])).

cnf(c_5251,plain,
    ( sK1(X0,X1,X2) = X3
    | r1_lattice3(X1,X2,sK2(X1,X4,sK1(X0,X1,X2))) != iProver_top
    | r1_lattice3(X1,X4,sK1(X0,X1,X2)) != iProver_top
    | sP0(X3,X1,X4) != iProver_top
    | sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK2(X1,X4,sK1(X0,X1,X2)),u1_struct_0(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5250])).

cnf(c_5261,plain,
    ( sK1(X0,sK5,sK7) = X1
    | sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | r1_lattice3(sK5,sK6,sK1(X0,sK5,sK7)) != iProver_top
    | sP0(X1,sK5,sK6) != iProver_top
    | sP0(X0,sK5,sK7) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK1(X0,sK5,sK7)),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(X0,sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5024,c_5251])).

cnf(c_2,plain,
    ( r1_lattice3(X0,X1,sK1(X2,X0,X1))
    | sP0(X2,X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3413,plain,
    ( r1_lattice3(X0,X1,sK1(X2,X0,X1)) = iProver_top
    | sP0(X2,X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3412,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,negated_conjecture,
    ( r1_lattice3(sK5,sK6,X0)
    | ~ r1_lattice3(sK5,sK7,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3406,plain,
    ( r1_lattice3(sK5,sK6,X0) = iProver_top
    | r1_lattice3(sK5,sK7,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3932,plain,
    ( r1_lattice3(sK5,sK6,sK1(X0,sK5,X1)) = iProver_top
    | r1_lattice3(sK5,sK7,sK1(X0,sK5,X1)) != iProver_top
    | sP0(X0,sK5,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_3406])).

cnf(c_4093,plain,
    ( r1_lattice3(sK5,sK6,sK1(X0,sK5,sK7)) = iProver_top
    | sP0(X0,sK5,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_3932])).

cnf(c_5635,plain,
    ( sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | sK1(X0,sK5,sK7) = X1
    | sP0(X1,sK5,sK6) != iProver_top
    | sP0(X0,sK5,sK7) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK1(X0,sK5,sK7)),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(X0,sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5261,c_4093])).

cnf(c_5636,plain,
    ( sK1(X0,sK5,sK7) = X1
    | sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | sP0(X1,sK5,sK6) != iProver_top
    | sP0(X0,sK5,sK7) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK1(X0,sK5,sK7)),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(X0,sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5635])).

cnf(c_5647,plain,
    ( sK1(X0,sK5,sK7) = X1
    | sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | sP0(X1,sK5,sK6) != iProver_top
    | sP0(X0,sK5,sK7) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK1(X0,sK5,sK7)),u1_struct_0(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5636,c_3412])).

cnf(c_5651,plain,
    ( sK1(X0,sK5,sK7) = X1
    | sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | r1_lattice3(sK5,sK6,sK1(X0,sK5,sK7)) != iProver_top
    | sP0(X1,sK5,sK6) != iProver_top
    | sP0(X0,sK5,sK7) = iProver_top
    | r2_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(sK1(X0,sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4370,c_5647])).

cnf(c_5885,plain,
    ( sP0(X0,sK5,sK7) = iProver_top
    | sP0(X1,sK5,sK6) != iProver_top
    | sK1(X0,sK5,sK7) = X1
    | sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | m1_subset_1(sK1(X0,sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5651,c_26,c_4093])).

cnf(c_5886,plain,
    ( sK1(X0,sK5,sK7) = X1
    | sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | sP0(X1,sK5,sK6) != iProver_top
    | sP0(X0,sK5,sK7) = iProver_top
    | m1_subset_1(sK1(X0,sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5885])).

cnf(c_5896,plain,
    ( sK1(X0,sK5,sK7) = X1
    | sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | sP0(X1,sK5,sK6) != iProver_top
    | sP0(X0,sK5,sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5886,c_3412])).

cnf(c_5900,plain,
    ( sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | sP0(X0,sK5,sK7) = iProver_top
    | r2_yellow_0(sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_5896])).

cnf(c_6038,plain,
    ( sP0(X0,sK5,sK7) = iProver_top
    | sK1(X0,sK5,sK7) = sK4(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5900,c_26])).

cnf(c_6039,plain,
    ( sK1(X0,sK5,sK7) = sK4(sK5,sK6)
    | sP0(X0,sK5,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_6038])).

cnf(c_8,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_291,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_292,plain,
    ( ~ r1_lattice3(sK5,X0,X1)
    | r1_lattice3(sK5,X0,sK3(sK5,X0,X1))
    | ~ sP0(X1,sK5,X0)
    | r2_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_3399,plain,
    ( r1_lattice3(sK5,X0,X1) != iProver_top
    | r1_lattice3(sK5,X0,sK3(sK5,X0,X1)) = iProver_top
    | sP0(X1,sK5,X0) != iProver_top
    | r2_yellow_0(sK5,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_9,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ sP0(X2,X0,X1)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_270,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ sP0(X2,X0,X1)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_271,plain,
    ( ~ r1_lattice3(sK5,X0,X1)
    | ~ sP0(X1,sK5,X0)
    | r2_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_3400,plain,
    ( r1_lattice3(sK5,X0,X1) != iProver_top
    | sP0(X1,sK5,X0) != iProver_top
    | r2_yellow_0(sK5,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_4265,plain,
    ( r1_lattice3(sK5,X0,X1) != iProver_top
    | r1_lattice3(sK5,sK6,sK3(sK5,X0,X1)) = iProver_top
    | r1_lattice3(sK5,sK7,sK3(sK5,X0,X1)) != iProver_top
    | sP0(X1,sK5,X0) != iProver_top
    | r2_yellow_0(sK5,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3400,c_3406])).

cnf(c_4276,plain,
    ( r1_lattice3(sK5,sK6,sK3(sK5,sK7,X0)) = iProver_top
    | r1_lattice3(sK5,sK7,X0) != iProver_top
    | sP0(X0,sK5,sK7) != iProver_top
    | r2_yellow_0(sK5,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_4265])).

cnf(c_14,negated_conjecture,
    ( ~ r2_yellow_0(sK5,sK7) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27,plain,
    ( r2_yellow_0(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5041,plain,
    ( sP0(X0,sK5,sK7) != iProver_top
    | r1_lattice3(sK5,sK7,X0) != iProver_top
    | r1_lattice3(sK5,sK6,sK3(sK5,sK7,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4276,c_27])).

cnf(c_5042,plain,
    ( r1_lattice3(sK5,sK6,sK3(sK5,sK7,X0)) = iProver_top
    | r1_lattice3(sK5,sK7,X0) != iProver_top
    | sP0(X0,sK5,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5041])).

cnf(c_11,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK4(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_240,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK4(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_241,plain,
    ( ~ r1_lattice3(sK5,X0,X1)
    | r1_orders_2(sK5,X1,sK4(sK5,X0))
    | ~ r2_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_3402,plain,
    ( r1_lattice3(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK5,X1,sK4(sK5,X0)) = iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_7,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ sP0(X2,X0,X1)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_312,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ sP0(X2,X0,X1)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_313,plain,
    ( ~ r1_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,sK3(sK5,X0,X1),X1)
    | ~ sP0(X1,sK5,X0)
    | r2_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_3398,plain,
    ( r1_lattice3(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK5,sK3(sK5,X0,X1),X1) != iProver_top
    | sP0(X1,sK5,X0) != iProver_top
    | r2_yellow_0(sK5,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_4087,plain,
    ( r1_lattice3(sK5,X0,sK3(sK5,X1,sK4(sK5,X0))) != iProver_top
    | r1_lattice3(sK5,X1,sK4(sK5,X0)) != iProver_top
    | sP0(sK4(sK5,X0),sK5,X1) != iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top
    | r2_yellow_0(sK5,X1) = iProver_top
    | m1_subset_1(sK3(sK5,X1,sK4(sK5,X0)),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3402,c_3398])).

cnf(c_448,plain,
    ( ~ r1_lattice3(sK5,X0,X1)
    | ~ r1_lattice3(sK5,X2,X3)
    | ~ sP0(X3,sK5,X2)
    | ~ r2_yellow_0(sK5,X0)
    | r2_yellow_0(sK5,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | sK3(sK5,X2,X3) != X1
    | sK4(sK5,X0) != X3
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_241,c_313])).

cnf(c_449,plain,
    ( ~ r1_lattice3(sK5,X0,sK3(sK5,X1,sK4(sK5,X0)))
    | ~ r1_lattice3(sK5,X1,sK4(sK5,X0))
    | ~ sP0(sK4(sK5,X0),sK5,X1)
    | ~ r2_yellow_0(sK5,X0)
    | r2_yellow_0(sK5,X1)
    | ~ m1_subset_1(sK3(sK5,X1,sK4(sK5,X0)),u1_struct_0(sK5))
    | ~ m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_13,plain,
    ( ~ r2_yellow_0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_216,plain,
    ( ~ r2_yellow_0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_217,plain,
    ( ~ r2_yellow_0(sK5,X0)
    | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_451,plain,
    ( ~ m1_subset_1(sK3(sK5,X1,sK4(sK5,X0)),u1_struct_0(sK5))
    | r2_yellow_0(sK5,X1)
    | ~ r2_yellow_0(sK5,X0)
    | ~ sP0(sK4(sK5,X0),sK5,X1)
    | ~ r1_lattice3(sK5,X1,sK4(sK5,X0))
    | ~ r1_lattice3(sK5,X0,sK3(sK5,X1,sK4(sK5,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_217])).

cnf(c_452,plain,
    ( ~ r1_lattice3(sK5,X0,sK3(sK5,X1,sK4(sK5,X0)))
    | ~ r1_lattice3(sK5,X1,sK4(sK5,X0))
    | ~ sP0(sK4(sK5,X0),sK5,X1)
    | ~ r2_yellow_0(sK5,X0)
    | r2_yellow_0(sK5,X1)
    | ~ m1_subset_1(sK3(sK5,X1,sK4(sK5,X0)),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_453,plain,
    ( r1_lattice3(sK5,X0,sK3(sK5,X1,sK4(sK5,X0))) != iProver_top
    | r1_lattice3(sK5,X1,sK4(sK5,X0)) != iProver_top
    | sP0(sK4(sK5,X0),sK5,X1) != iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top
    | r2_yellow_0(sK5,X1) = iProver_top
    | m1_subset_1(sK3(sK5,X1,sK4(sK5,X0)),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_4352,plain,
    ( m1_subset_1(sK3(sK5,X1,sK4(sK5,X0)),u1_struct_0(sK5)) != iProver_top
    | r2_yellow_0(sK5,X1) = iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top
    | sP0(sK4(sK5,X0),sK5,X1) != iProver_top
    | r1_lattice3(sK5,X1,sK4(sK5,X0)) != iProver_top
    | r1_lattice3(sK5,X0,sK3(sK5,X1,sK4(sK5,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4087,c_453])).

cnf(c_4353,plain,
    ( r1_lattice3(sK5,X0,sK3(sK5,X1,sK4(sK5,X0))) != iProver_top
    | r1_lattice3(sK5,X1,sK4(sK5,X0)) != iProver_top
    | sP0(sK4(sK5,X0),sK5,X1) != iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top
    | r2_yellow_0(sK5,X1) = iProver_top
    | m1_subset_1(sK3(sK5,X1,sK4(sK5,X0)),u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4352])).

cnf(c_5052,plain,
    ( r1_lattice3(sK5,sK7,sK4(sK5,sK6)) != iProver_top
    | sP0(sK4(sK5,sK6),sK5,sK7) != iProver_top
    | r2_yellow_0(sK5,sK6) != iProver_top
    | r2_yellow_0(sK5,sK7) = iProver_top
    | m1_subset_1(sK3(sK5,sK7,sK4(sK5,sK6)),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5042,c_4353])).

cnf(c_845,plain,
    ( m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5))
    | sK6 != X0
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_217])).

cnf(c_846,plain,
    ( m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_847,plain,
    ( m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_12,plain,
    ( r1_lattice3(X0,X1,sK4(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_228,plain,
    ( r1_lattice3(X0,X1,sK4(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_229,plain,
    ( r1_lattice3(sK5,X0,sK4(sK5,X0))
    | ~ r2_yellow_0(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_3403,plain,
    ( r1_lattice3(sK5,X0,sK4(sK5,X0)) = iProver_top
    | r2_yellow_0(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_3629,plain,
    ( r1_lattice3(sK5,sK7,sK4(sK5,sK6)) = iProver_top
    | r2_yellow_0(sK5,sK6) != iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3403,c_3405])).

cnf(c_3610,plain,
    ( ~ r1_lattice3(sK5,X0,sK4(sK5,sK6))
    | ~ sP0(sK4(sK5,sK6),sK5,X0)
    | r2_yellow_0(sK5,X0)
    | m1_subset_1(sK3(sK5,X0,sK4(sK5,sK6)),u1_struct_0(sK5))
    | ~ m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_3738,plain,
    ( ~ r1_lattice3(sK5,sK7,sK4(sK5,sK6))
    | ~ sP0(sK4(sK5,sK6),sK5,sK7)
    | r2_yellow_0(sK5,sK7)
    | m1_subset_1(sK3(sK5,sK7,sK4(sK5,sK6)),u1_struct_0(sK5))
    | ~ m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3610])).

cnf(c_3739,plain,
    ( r1_lattice3(sK5,sK7,sK4(sK5,sK6)) != iProver_top
    | sP0(sK4(sK5,sK6),sK5,sK7) != iProver_top
    | r2_yellow_0(sK5,sK7) = iProver_top
    | m1_subset_1(sK3(sK5,sK7,sK4(sK5,sK6)),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3738])).

cnf(c_5369,plain,
    ( sP0(sK4(sK5,sK6),sK5,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5052,c_26,c_27,c_847,c_3629,c_3739])).

cnf(c_6049,plain,
    ( sK1(sK4(sK5,sK6),sK5,sK7) = sK4(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_6039,c_5369])).

cnf(c_0,plain,
    ( sP0(X0,X1,X2)
    | sK1(X0,X1,X2) != X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3943,plain,
    ( sP0(sK4(sK5,sK6),sK5,sK7)
    | sK1(sK4(sK5,sK6),sK5,sK7) != sK4(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3947,plain,
    ( sK1(sK4(sK5,sK6),sK5,sK7) != sK4(sK5,sK6)
    | sP0(sK4(sK5,sK6),sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3943])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6049,c_5369,c_3947])).


%------------------------------------------------------------------------------
