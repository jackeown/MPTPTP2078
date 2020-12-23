%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1540+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:49 EST 2020

% Result     : Theorem 12.04s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :  274 (8297 expanded)
%              Number of clauses        :  196 (2008 expanded)
%              Number of leaves         :   15 (2634 expanded)
%              Depth                    :   37
%              Number of atoms          : 1799 (109176 expanded)
%              Number of equality atoms :  607 (13113 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal clause size      :   28 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k10_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k10_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X6)
                                  & r1_orders_2(X0,X1,X6) )
                               => r1_orders_2(X0,X5,X6) ) )
                          & r1_orders_2(X0,X2,X5)
                          & r1_orders_2(X0,X1,X5) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k10_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X5,X6)
                          | ~ r1_orders_2(X0,X2,X6)
                          | ~ r1_orders_2(X0,X1,X6)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X5)
                      & r1_orders_2(X0,X1,X5) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k10_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X5,X6)
                          | ~ r1_orders_2(X0,X2,X6)
                          | ~ r1_orders_2(X0,X1,X6)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X5)
                      & r1_orders_2(X0,X1,X5) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( k10_lattice3(X0,X1,X2) = X5
          <=> ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r1_orders_2(X0,X2,X6)
                  | ~ r1_orders_2(X0,X1,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r1_orders_2(X0,X2,X5)
              & r1_orders_2(X0,X1,X5) ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f10,f19])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                    & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                    & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                    & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f28])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK5(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK5(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK5(X0,X1))
              & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f33,f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) )
                       => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) )
                       => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X5)
                                  & r1_orders_2(X0,X1,X5) )
                               => r1_orders_2(X0,X3,X5) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                        | k10_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X3,X5)
                            & r1_orders_2(X0,X2,X5)
                            & r1_orders_2(X0,X1,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X2,X3)
                        | ~ r1_orders_2(X0,X1,X3) )
                      & r1_yellow_0(X0,k2_tarski(X1,X2))
                      & k10_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                        | k10_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X3,X5)
                            & r1_orders_2(X0,X2,X5)
                            & r1_orders_2(X0,X1,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X2,X3)
                        | ~ r1_orders_2(X0,X1,X3) )
                      & r1_yellow_0(X0,k2_tarski(X1,X2))
                      & k10_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f21,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( ? [X5] :
              ( ~ r1_orders_2(X0,X3,X5)
              & r1_orders_2(X0,X2,X5)
              & r1_orders_2(X0,X1,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X2,X3)
          | ~ r1_orders_2(X0,X1,X3) )
        & r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ~ sP1(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                        | k10_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | sP1(X3,X0,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                | k10_lattice3(X0,X1,X2) != X3 )
              & ! [X4] :
                  ( r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r1_orders_2(X0,X1,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r1_orders_2(X0,X2,X3)
              & r1_orders_2(X0,X1,X3) )
            | sP1(X3,X0,X2,X1) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
              | k10_lattice3(X0,X1,X2) != sK10 )
            & ! [X4] :
                ( r1_orders_2(X0,sK10,X4)
                | ~ r1_orders_2(X0,X2,X4)
                | ~ r1_orders_2(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_orders_2(X0,X2,sK10)
            & r1_orders_2(X0,X1,sK10) )
          | sP1(sK10,X0,X2,X1) )
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                    | k10_lattice3(X0,X1,X2) != X3 )
                  & ! [X4] :
                      ( r1_orders_2(X0,X3,X4)
                      | ~ r1_orders_2(X0,X2,X4)
                      | ~ r1_orders_2(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X3) )
                | sP1(X3,X0,X2,X1) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,sK9))
                  | k10_lattice3(X0,X1,sK9) != X3 )
                & ! [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,sK9,X4)
                    | ~ r1_orders_2(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_orders_2(X0,sK9,X3)
                & r1_orders_2(X0,X1,X3) )
              | sP1(X3,X0,sK9,X1) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                        | k10_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | sP1(X3,X0,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(sK8,X2))
                      | k10_lattice3(X0,sK8,X2) != X3 )
                    & ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,sK8,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,sK8,X3) )
                  | sP1(X3,X0,X2,sK8) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                          | k10_lattice3(X0,X1,X2) != X3 )
                        & ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | sP1(X3,X0,X2,X1) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(sK7,k2_tarski(X1,X2))
                        | k10_lattice3(sK7,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(sK7,X3,X4)
                          | ~ r1_orders_2(sK7,X2,X4)
                          | ~ r1_orders_2(sK7,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(sK7)) )
                      & r1_orders_2(sK7,X2,X3)
                      & r1_orders_2(sK7,X1,X3) )
                    | sP1(X3,sK7,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(sK7)) )
              & m1_subset_1(X2,u1_struct_0(sK7)) )
          & m1_subset_1(X1,u1_struct_0(sK7)) )
      & l1_orders_2(sK7)
      & v5_orders_2(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ( ( ~ r1_yellow_0(sK7,k2_tarski(sK8,sK9))
          | k10_lattice3(sK7,sK8,sK9) != sK10 )
        & ! [X4] :
            ( r1_orders_2(sK7,sK10,X4)
            | ~ r1_orders_2(sK7,sK9,X4)
            | ~ r1_orders_2(sK7,sK8,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK7)) )
        & r1_orders_2(sK7,sK9,sK10)
        & r1_orders_2(sK7,sK8,sK10) )
      | sP1(sK10,sK7,sK9,sK8) )
    & m1_subset_1(sK10,u1_struct_0(sK7))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l1_orders_2(sK7)
    & v5_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f22,f42,f41,f40,f39])).

fof(f81,plain,(
    ! [X4] :
      ( r1_orders_2(sK7,sK10,X4)
      | ~ r1_orders_2(sK7,sK9,X4)
      | ~ r1_orders_2(sK7,sK8,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK7))
      | sP1(sK10,sK7,sK9,sK8) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,
    ( r1_orders_2(sK7,sK8,sK10)
    | sP1(sK10,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,
    ( r1_orders_2(sK7,sK9,sK10)
    | sP1(sK10,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,
    ( ~ r1_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k10_lattice3(sK7,sK8,sK9) != sK10
    | sP1(sK10,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( ? [X5] :
              ( ~ r1_orders_2(X0,X3,X5)
              & r1_orders_2(X0,X2,X5)
              & r1_orders_2(X0,X1,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X2,X3)
          | ~ r1_orders_2(X0,X1,X3) )
        & r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ~ sP1(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ? [X4] :
              ( ~ r1_orders_2(X1,X0,X4)
              & r1_orders_2(X1,X2,X4)
              & r1_orders_2(X1,X3,X4)
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r1_orders_2(X1,X2,X0)
          | ~ r1_orders_2(X1,X3,X0) )
        & r1_yellow_0(X1,k2_tarski(X3,X2))
        & k10_lattice3(X1,X3,X2) = X0 )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X0,X4)
          & r1_orders_2(X1,X2,X4)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2,X3))
        & r1_orders_2(X1,X2,sK6(X0,X1,X2,X3))
        & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2,X3))
            & r1_orders_2(X1,X2,sK6(X0,X1,X2,X3))
            & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
            & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r1_orders_2(X1,X2,X0)
          | ~ r1_orders_2(X1,X3,X0) )
        & r1_yellow_0(X1,k2_tarski(X3,X2))
        & k10_lattice3(X1,X3,X2) = X0 )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X1,X3,X2) = X0
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k10_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X5,X6)
                  & r1_orders_2(X0,X2,X6)
                  & r1_orders_2(X0,X1,X6)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X5)
              | ~ r1_orders_2(X0,X1,X5) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X5,X6)
                    | ~ r1_orders_2(X0,X2,X6)
                    | ~ r1_orders_2(X0,X1,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X2,X5)
                & r1_orders_2(X0,X1,X5) )
              | k10_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k10_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X5,X6)
                  & r1_orders_2(X0,X2,X6)
                  & r1_orders_2(X0,X1,X6)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X5)
              | ~ r1_orders_2(X0,X1,X5) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X5,X6)
                    | ~ r1_orders_2(X0,X2,X6)
                    | ~ r1_orders_2(X0,X1,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X2,X5)
                & r1_orders_2(X0,X1,X5) )
              | k10_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k10_lattice3(X0,X2,X1) = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X1,X4)
                  & r1_orders_2(X0,X2,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X1,X3)
              | ~ r1_orders_2(X0,X2,X3) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X3,X5)
                    | ~ r1_orders_2(X0,X1,X5)
                    | ~ r1_orders_2(X0,X2,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X1,X3)
                & r1_orders_2(X0,X2,X3) )
              | k10_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X1,X4)
          & r1_orders_2(X0,X2,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK2(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK2(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK2(X0,X1,X2,X3))
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k10_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,X3,sK2(X0,X1,X2,X3))
                & r1_orders_2(X0,X1,sK2(X0,X1,X2,X3))
                & r1_orders_2(X0,X2,sK2(X0,X1,X2,X3))
                & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X1,X3)
              | ~ r1_orders_2(X0,X2,X3) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X3,X5)
                    | ~ r1_orders_2(X0,X1,X5)
                    | ~ r1_orders_2(X0,X2,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X1,X3)
                & r1_orders_2(X0,X2,X3) )
              | k10_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,X2,sK2(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,X1,sK2(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,sK2(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X1,k2_tarski(X3,X2))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK5(X0,X1),X5)
      | ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X1,X2,X0)
      | ~ r1_orders_2(X1,X3,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X2,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X1,X2,X0)
      | ~ r1_orders_2(X1,X3,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X2,X1),X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X0)
      | ~ r1_orders_2(X1,X3,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X1,X2,X0)
      | ~ r1_orders_2(X1,X3,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X2,X1))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X3,sK3(X0,X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_372,plain,
    ( sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | ~ r1_orders_2(X0_49,X2_50,sK3(X0_49,X1_50,X0_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3029,plain,
    ( sP0(sK7,X0_50,X1_50)
    | ~ r1_orders_2(sK7,X0_50,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ r1_orders_2(sK7,X1_50,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ r1_orders_2(sK7,sK5(sK7,k2_tarski(sK8,sK9)),sK3(sK7,X1_50,X0_50,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_37286,plain,
    ( sP0(sK7,sK9,sK8)
    | ~ r1_orders_2(sK7,sK5(sK7,k2_tarski(sK8,sK9)),sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ r1_orders_2(sK7,sK9,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ r1_orders_2(sK7,sK8,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_3029])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK4(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_366,plain,
    ( ~ r2_lattice3(X0_49,X0_52,X0_50)
    | r2_lattice3(X0_49,X0_52,sK4(X0_49,X0_52,X0_50))
    | r1_yellow_0(X0_49,X0_52)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1053,plain,
    ( r2_lattice3(X0_49,X0_52,X0_50) != iProver_top
    | r2_lattice3(X0_49,X0_52,sK4(X0_49,X0_52,X0_50)) = iProver_top
    | r1_yellow_0(X0_49,X0_52) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_20,plain,
    ( ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_359,plain,
    ( ~ r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50)
    | r1_orders_2(X0_49,X0_50,X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1060,plain,
    ( r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_4899,plain,
    ( r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50)) = iProver_top
    | r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50),u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1060])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_365,plain,
    ( ~ r2_lattice3(X0_49,X0_52,X0_50)
    | r1_yellow_0(X0_49,X0_52)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | m1_subset_1(sK4(X0_49,X0_52,X0_50),u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2043,plain,
    ( ~ r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50)
    | r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | m1_subset_1(sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50),u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_2049,plain,
    ( r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50),u1_struct_0(X0_49)) = iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2043])).

cnf(c_20453,plain,
    ( m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50)) = iProver_top
    | r1_orders_2(X0_49,X0_50,sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50)) = iProver_top
    | r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4899,c_2049])).

cnf(c_20454,plain,
    ( r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50)) = iProver_top
    | r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_20453])).

cnf(c_31,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,sK10,X0)
    | ~ r1_orders_2(sK7,sK9,X0)
    | ~ r1_orders_2(sK7,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_348,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,sK10,X0_50)
    | ~ r1_orders_2(sK7,sK9,X0_50)
    | ~ r1_orders_2(sK7,sK8,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1071,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK10,X0_50) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_367,plain,
    ( ~ r2_lattice3(X0_49,X0_52,X0_50)
    | ~ r1_orders_2(X0_49,X0_50,sK4(X0_49,X0_52,X0_50))
    | r1_yellow_0(X0_49,X0_52)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1052,plain,
    ( r2_lattice3(X0_49,X0_52,X0_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,sK4(X0_49,X0_52,X0_50)) != iProver_top
    | r1_yellow_0(X0_49,X0_52) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_4681,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r2_lattice3(sK7,X0_52,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_yellow_0(sK7,X0_52) = iProver_top
    | m1_subset_1(sK4(sK7,X0_52,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1052])).

cnf(c_38,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( v5_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( l1_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5028,plain,
    ( m1_subset_1(sK4(sK7,X0_52,sK10),u1_struct_0(sK7)) != iProver_top
    | r1_yellow_0(sK7,X0_52) = iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_orders_2(sK7,sK9,sK4(sK7,X0_52,sK10)) != iProver_top
    | r2_lattice3(sK7,X0_52,sK10) != iProver_top
    | sP1(sK10,sK7,sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4681,c_39,c_40,c_43])).

cnf(c_5029,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r2_lattice3(sK7,X0_52,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_yellow_0(sK7,X0_52) = iProver_top
    | m1_subset_1(sK4(sK7,X0_52,sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5028])).

cnf(c_20472,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r2_lattice3(sK7,k2_tarski(sK9,X0_50),sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,k2_tarski(sK9,X0_50),sK10)) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK9,X0_50)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(sK9,X0_50),sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_20454,c_5029])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_41,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_42,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,sK8,sK10) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_44,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK8,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,sK9,sK10) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_45,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | ~ r1_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k10_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_349,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | ~ r1_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k10_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_481,plain,
    ( k10_lattice3(sK7,sK8,sK9) != sK10
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_2384,plain,
    ( ~ r2_lattice3(sK7,k2_tarski(sK8,sK9),X0_50)
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,k2_tarski(sK8,sK9),X0_50),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_2043])).

cnf(c_2385,plain,
    ( r2_lattice3(sK7,k2_tarski(sK8,sK9),X0_50) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(sK8,sK9),X0_50),u1_struct_0(sK7)) = iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2384])).

cnf(c_2387,plain,
    ( r2_lattice3(sK7,k2_tarski(sK8,sK9),sK10) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(sK8,sK9),sK10),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2385])).

cnf(c_18,plain,
    ( r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_361,plain,
    ( r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2866,plain,
    ( r2_lattice3(sK7,k2_tarski(sK8,sK9),X0_50)
    | ~ r1_orders_2(sK7,sK9,X0_50)
    | ~ r1_orders_2(sK7,sK8,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_2867,plain,
    ( r2_lattice3(sK7,k2_tarski(sK8,sK9),X0_50) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2866])).

cnf(c_2869,plain,
    ( r2_lattice3(sK7,k2_tarski(sK8,sK9),sK10) = iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK10) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,sK3(X0,X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_371,plain,
    ( sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | r1_orders_2(X0_49,X0_50,sK3(X0_49,X1_50,X0_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1048,plain,
    ( sP0(X0_49,X0_50,X1_50) = iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,sK3(X0_49,X1_50,X0_50,X2_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_29,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | k10_lattice3(X1,X3,X2) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_350,plain,
    ( ~ sP1(X0_50,X0_49,X1_50,X2_50)
    | k10_lattice3(X0_49,X2_50,X1_50) = X0_50 ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1069,plain,
    ( k10_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP1(X2_50,X0_49,X1_50,X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_1844,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK10,X0_50) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1069])).

cnf(c_7237,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | sP0(sK7,sK9,X0_50) = iProver_top
    | r1_orders_2(sK7,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK7,sK10,sK3(sK7,X0_50,sK9,X1_50)) = iProver_top
    | r1_orders_2(sK7,sK9,X1_50) != iProver_top
    | r1_orders_2(sK7,sK8,sK3(sK7,X0_50,sK9,X1_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X0_50,sK9,X1_50),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_1844])).

cnf(c_1571,plain,
    ( ~ sP1(sK10,sK7,sK9,sK8)
    | k10_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_346,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,sK8,sK10) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1073,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK8,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1667,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK8,sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1069])).

cnf(c_1677,plain,
    ( r1_orders_2(sK7,sK8,sK10)
    | k10_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1667])).

cnf(c_347,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,sK9,sK10) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1072,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_1668,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK9,sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1069])).

cnf(c_1678,plain,
    ( r1_orders_2(sK7,sK9,sK10)
    | k10_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1668])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X2,sK2(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_377,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | r1_orders_2(X0_49,X1_50,sK2(X0_49,X0_50,X1_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k10_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1042,plain,
    ( k10_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP0(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,sK2(X0_49,X1_50,X0_50,X2_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_1,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,sK2(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_378,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | r1_orders_2(X0_49,X0_50,sK2(X0_49,X0_50,X1_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k10_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1041,plain,
    ( k10_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP0(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,sK2(X0_49,X1_50,X0_50,X2_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_2491,plain,
    ( k10_lattice3(sK7,X0_50,sK9) = X1_50
    | k10_lattice3(sK7,sK8,sK9) = sK10
    | sP0(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK7,sK10,sK2(sK7,sK9,X0_50,X1_50)) = iProver_top
    | r1_orders_2(sK7,sK9,X1_50) != iProver_top
    | r1_orders_2(sK7,sK8,sK2(sK7,sK9,X0_50,X1_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK2(sK7,sK9,X0_50,X1_50),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_1844])).

cnf(c_3464,plain,
    ( k10_lattice3(sK7,sK8,sK9) = X0_50
    | k10_lattice3(sK7,sK8,sK9) = sK10
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK2(sK7,sK9,sK8,X0_50)) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK2(sK7,sK9,sK8,X0_50),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_2491])).

cnf(c_3,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_376,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | m1_subset_1(sK2(X0_49,X0_50,X1_50,X2_50),u1_struct_0(X0_49))
    | k10_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1043,plain,
    ( k10_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP0(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(sK2(X0_49,X1_50,X0_50,X2_50),u1_struct_0(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_0,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X3,sK2(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_379,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | ~ r1_orders_2(X0_49,X2_50,sK2(X0_49,X0_50,X1_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k10_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1040,plain,
    ( k10_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP0(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,sK2(X0_49,X1_50,X0_50,X2_50)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1842,plain,
    ( k10_lattice3(sK7,X0_50,X1_50) = sK10
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,X1_50,X0_50) != iProver_top
    | r1_orders_2(sK7,X1_50,sK10) != iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK2(sK7,X1_50,X0_50,sK10)) != iProver_top
    | r1_orders_2(sK7,sK8,sK2(sK7,X1_50,X0_50,sK10)) != iProver_top
    | m1_subset_1(sK2(sK7,X1_50,X0_50,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1040])).

cnf(c_2470,plain,
    ( m1_subset_1(sK2(sK7,X1_50,X0_50,sK10),u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,sK8,sK2(sK7,X1_50,X0_50,sK10)) != iProver_top
    | r1_orders_2(sK7,sK9,sK2(sK7,X1_50,X0_50,sK10)) != iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,X1_50,sK10) != iProver_top
    | sP0(sK7,X1_50,X0_50) != iProver_top
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | k10_lattice3(sK7,X0_50,X1_50) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1842,c_43])).

cnf(c_2471,plain,
    ( k10_lattice3(sK7,X0_50,X1_50) = sK10
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,X1_50,X0_50) != iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,X1_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK2(sK7,X1_50,X0_50,sK10)) != iProver_top
    | r1_orders_2(sK7,sK8,sK2(sK7,X1_50,X0_50,sK10)) != iProver_top
    | m1_subset_1(sK2(sK7,X1_50,X0_50,sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2470])).

cnf(c_2493,plain,
    ( k10_lattice3(sK7,X0_50,sK9) = sK10
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK2(sK7,sK9,X0_50,sK10)) != iProver_top
    | m1_subset_1(sK2(sK7,sK9,X0_50,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_2471])).

cnf(c_3075,plain,
    ( m1_subset_1(sK2(sK7,sK9,X0_50,sK10),u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,sK8,sK2(sK7,sK9,X0_50,sK10)) != iProver_top
    | k10_lattice3(sK7,X0_50,sK9) = sK10
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2493,c_43,c_45])).

cnf(c_3076,plain,
    ( k10_lattice3(sK7,X0_50,sK9) = sK10
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK2(sK7,sK9,X0_50,sK10)) != iProver_top
    | m1_subset_1(sK2(sK7,sK9,X0_50,sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3075])).

cnf(c_3466,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK10) != iProver_top
    | m1_subset_1(sK2(sK7,sK9,sK8,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_3076])).

cnf(c_1572,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | sP1(sK10,sK7,sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_5537,plain,
    ( m1_subset_1(sK2(sK7,sK9,sK8,sK10),u1_struct_0(sK7)) != iProver_top
    | sP0(sK7,sK9,sK8) != iProver_top
    | k10_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3466,c_43,c_1572,c_1667,c_1668])).

cnf(c_5538,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | sP0(sK7,sK9,sK8) != iProver_top
    | m1_subset_1(sK2(sK7,sK9,sK8,sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5537])).

cnf(c_5544,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK10) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_5538])).

cnf(c_5971,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | k10_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3464,c_43,c_1667,c_1668,c_5544])).

cnf(c_5972,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10
    | sP0(sK7,sK9,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_5971])).

cnf(c_5973,plain,
    ( ~ sP0(sK7,sK9,sK8)
    | k10_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5972])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X2,sK3(X0,X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_370,plain,
    ( sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | r1_orders_2(X0_49,X1_50,sK3(X0_49,X1_50,X0_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1049,plain,
    ( sP0(X0_49,X0_50,X1_50) = iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,sK3(X0_49,X1_50,X0_50,X2_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_1047,plain,
    ( sP0(X0_49,X0_50,X1_50) = iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,sK3(X0_49,X1_50,X0_50,X2_50)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_6981,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,X1_50,sK10) != iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK3(sK7,X1_50,X0_50,sK10)) != iProver_top
    | r1_orders_2(sK7,sK8,sK3(sK7,X1_50,X0_50,sK10)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X1_50,X0_50,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1047])).

cnf(c_7498,plain,
    ( m1_subset_1(sK3(sK7,X1_50,X0_50,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,sK8,sK3(sK7,X1_50,X0_50,sK10)) != iProver_top
    | r1_orders_2(sK7,sK9,sK3(sK7,X1_50,X0_50,sK10)) != iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,X1_50,sK10) != iProver_top
    | sP0(sK7,X0_50,X1_50) = iProver_top
    | sP1(sK10,sK7,sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6981,c_39,c_40,c_43])).

cnf(c_7499,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,X1_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK3(sK7,X1_50,X0_50,sK10)) != iProver_top
    | r1_orders_2(sK7,sK8,sK3(sK7,X1_50,X0_50,sK10)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X1_50,X0_50,sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7498])).

cnf(c_7514,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,sK9,X0_50) = iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK3(sK7,X0_50,sK9,sK10)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X0_50,sK9,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_7499])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X2,X1,X3),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_369,plain,
    ( sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | m1_subset_1(sK3(X0_49,X1_50,X0_50,X2_50),u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4392,plain,
    ( sP0(sK7,sK9,X0_50)
    | ~ r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,sK9,sK10)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | m1_subset_1(sK3(sK7,X0_50,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_4393,plain,
    ( sP0(sK7,sK9,X0_50) = iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X0_50,sK9,sK10),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4392])).

cnf(c_7715,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,sK8,sK3(sK7,X0_50,sK9,sK10)) != iProver_top
    | sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,sK9,X0_50) = iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7514,c_39,c_40,c_42,c_43,c_45,c_4393])).

cnf(c_7716,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,sK9,X0_50) = iProver_top
    | r1_orders_2(sK7,X0_50,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK3(sK7,X0_50,sK9,sK10)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7715])).

cnf(c_7726,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | sP0(sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK10) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_7716])).

cnf(c_7727,plain,
    ( sP1(sK10,sK7,sK9,sK8)
    | sP0(sK7,sK9,sK8)
    | ~ r1_orders_2(sK7,sK9,sK10)
    | ~ r1_orders_2(sK7,sK8,sK10)
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7726])).

cnf(c_7729,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7237,c_38,c_37,c_36,c_35,c_34,c_1571,c_1677,c_1678,c_5973,c_7727])).

cnf(c_19,plain,
    ( ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_360,plain,
    ( ~ r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50)
    | r1_orders_2(X0_49,X1_50,X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1059,plain,
    ( r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_4852,plain,
    ( r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50)) = iProver_top
    | r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50),u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1059])).

cnf(c_16140,plain,
    ( m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50)) = iProver_top
    | r1_orders_2(X0_49,X1_50,sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50)) = iProver_top
    | r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4852,c_2049])).

cnf(c_16141,plain,
    ( r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,sK4(X0_49,k2_tarski(X0_50,X1_50),X2_50)) = iProver_top
    | r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | l1_orders_2(X0_49) != iProver_top
    | v5_orders_2(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_16140])).

cnf(c_16160,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r2_lattice3(sK7,k2_tarski(X0_50,sK9),sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,k2_tarski(X0_50,sK9),sK10)) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(X0_50,sK9)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(X0_50,sK9),sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_16141,c_5029])).

cnf(c_28,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | r1_yellow_0(X1,k2_tarski(X3,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_351,plain,
    ( ~ sP1(X0_50,X0_49,X1_50,X2_50)
    | r1_yellow_0(X0_49,k2_tarski(X2_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1068,plain,
    ( sP1(X0_50,X0_49,X1_50,X2_50) != iProver_top
    | r1_yellow_0(X0_49,k2_tarski(X2_50,X1_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_1843,plain,
    ( r1_orders_2(sK7,sK10,X0_50) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1068])).

cnf(c_4680,plain,
    ( r2_lattice3(sK7,X0_52,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_yellow_0(sK7,X0_52) = iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(sK4(sK7,X0_52,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_1052])).

cnf(c_1568,plain,
    ( ~ sP1(sK10,sK7,sK9,sK8)
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_1569,plain,
    ( sP1(sK10,sK7,sK9,sK8) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_5041,plain,
    ( m1_subset_1(sK4(sK7,X0_52,sK10),u1_struct_0(sK7)) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | r1_yellow_0(sK7,X0_52) = iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_orders_2(sK7,sK9,sK4(sK7,X0_52,sK10)) != iProver_top
    | r2_lattice3(sK7,X0_52,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4680,c_39,c_40,c_43,c_1569,c_4681])).

cnf(c_5042,plain,
    ( r2_lattice3(sK7,X0_52,sK10) != iProver_top
    | r1_orders_2(sK7,sK9,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,X0_52,sK10)) != iProver_top
    | r1_yellow_0(sK7,X0_52) = iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(sK4(sK7,X0_52,sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5041])).

cnf(c_16159,plain,
    ( r2_lattice3(sK7,k2_tarski(X0_50,sK9),sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,k2_tarski(X0_50,sK9),sK10)) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(X0_50,sK9)) = iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(X0_50,sK9),sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_16141,c_5042])).

cnf(c_29579,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r2_lattice3(sK7,k2_tarski(X0_50,sK9),sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK4(sK7,k2_tarski(X0_50,sK9),sK10)) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(X0_50,sK9)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(X0_50,sK9),sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16160,c_38,c_39,c_37,c_40,c_36,c_35,c_42,c_34,c_43,c_481,c_1571,c_1677,c_1678,c_5973,c_7727,c_16159])).

cnf(c_29591,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top
    | r2_lattice3(sK7,k2_tarski(sK8,sK9),sK10) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(sK8,sK9),sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | v5_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_20454,c_29579])).

cnf(c_29594,plain,
    ( sP1(sK10,sK7,sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20472,c_38,c_39,c_37,c_40,c_36,c_41,c_35,c_42,c_34,c_43,c_44,c_45,c_481,c_1571,c_1677,c_1678,c_2387,c_2869,c_5973,c_7727,c_29591])).

cnf(c_29596,plain,
    ( sP1(sK10,sK7,sK9,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29594])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK5(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_364,plain,
    ( ~ r2_lattice3(X0_49,X0_52,X0_50)
    | r1_orders_2(X0_49,sK5(X0_49,X0_52),X0_50)
    | ~ r1_yellow_0(X0_49,X0_52)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2389,plain,
    ( ~ r2_lattice3(X0_49,k2_tarski(X0_50,X1_50),X2_50)
    | r1_orders_2(X0_49,sK5(X0_49,k2_tarski(X0_50,X1_50)),X2_50)
    | ~ r1_yellow_0(X0_49,k2_tarski(X0_50,X1_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_25662,plain,
    ( ~ r2_lattice3(sK7,k2_tarski(sK8,sK9),sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(sK8,sK9)),sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ r1_yellow_0(sK7,k2_tarski(sK8,sK9))
    | ~ m1_subset_1(sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_2389])).

cnf(c_18142,plain,
    ( r2_lattice3(sK7,k2_tarski(sK8,sK9),sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ r1_orders_2(sK7,sK9,sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ r1_orders_2(sK7,sK8,sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ m1_subset_1(sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_2866])).

cnf(c_26,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X0)
    | ~ r1_orders_2(X1,X3,X0)
    | r1_orders_2(X1,X3,sK6(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_353,plain,
    ( ~ sP1(X0_50,X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X1_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | r1_orders_2(X0_49,X2_50,sK6(X0_50,X0_49,X1_50,X2_50)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1066,plain,
    ( sP1(X0_50,X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,sK6(X0_50,X0_49,X1_50,X2_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_25,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X0)
    | ~ r1_orders_2(X1,X3,X0)
    | r1_orders_2(X1,X2,sK6(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_354,plain,
    ( ~ sP1(X0_50,X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X1_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | r1_orders_2(X0_49,X1_50,sK6(X0_50,X0_49,X1_50,X2_50)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1065,plain,
    ( sP1(X0_50,X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,sK6(X0_50,X0_49,X1_50,X2_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_4,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,k10_lattice3(X0,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_375,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | r1_orders_2(X0_49,k10_lattice3(X0_49,X1_50,X0_50),X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(k10_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1044,plain,
    ( sP0(X0_49,X0_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,k10_lattice3(X0_49,X1_50,X0_50),X2_50) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(k10_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_7743,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,k10_lattice3(sK7,sK8,sK9),X0_50) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7729,c_1044])).

cnf(c_7767,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,X0_50) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7743,c_7729])).

cnf(c_8467,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK10,X0_50) = iProver_top
    | sP0(sK7,sK9,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7767,c_43])).

cnf(c_8468,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,X0_50) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8467])).

cnf(c_8477,plain,
    ( sP1(X0_50,sK7,sK9,X1_50) != iProver_top
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,X1_50,X0_50) != iProver_top
    | r1_orders_2(sK7,sK10,sK6(X0_50,sK7,sK9,X1_50)) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,sK6(X0_50,sK7,sK9,X1_50)) != iProver_top
    | m1_subset_1(sK6(X0_50,sK7,sK9,X1_50),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_8468])).

cnf(c_27,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X0)
    | ~ r1_orders_2(X1,X3,X0)
    | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_352,plain,
    ( ~ sP1(X0_50,X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X1_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | m1_subset_1(sK6(X0_50,X0_49,X1_50,X2_50),u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1067,plain,
    ( sP1(X0_50,X0_49,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,X0_50) != iProver_top
    | m1_subset_1(sK6(X0_50,X0_49,X1_50,X2_50),u1_struct_0(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_8945,plain,
    ( sP1(X0_50,sK7,sK9,X1_50) != iProver_top
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,X1_50,X0_50) != iProver_top
    | r1_orders_2(sK7,sK10,sK6(X0_50,sK7,sK9,X1_50)) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,sK6(X0_50,sK7,sK9,X1_50)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8477,c_1067])).

cnf(c_8949,plain,
    ( sP1(X0_50,sK7,sK9,sK8) != iProver_top
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK6(X0_50,sK7,sK9,sK8)) = iProver_top
    | r1_orders_2(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,sK8,X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_8945])).

cnf(c_24,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X0)
    | ~ r1_orders_2(X1,X3,X0)
    | ~ r1_orders_2(X1,X0,sK6(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_355,plain,
    ( ~ sP1(X0_50,X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X1_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X0_50,sK6(X0_50,X0_49,X1_50,X2_50)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1800,plain,
    ( ~ sP1(sK10,sK7,X0_50,X1_50)
    | ~ r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,X1_50,sK10)
    | ~ r1_orders_2(sK7,sK10,sK6(sK10,sK7,X0_50,X1_50)) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_2900,plain,
    ( ~ sP1(sK10,sK7,sK9,sK8)
    | ~ r1_orders_2(sK7,sK10,sK6(sK10,sK7,sK9,sK8))
    | ~ r1_orders_2(sK7,sK9,sK10)
    | ~ r1_orders_2(sK7,sK8,sK10) ),
    inference(instantiation,[status(thm)],[c_1800])).

cnf(c_2901,plain,
    ( sP1(sK10,sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK6(sK10,sK7,sK9,sK8)) != iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2900])).

cnf(c_3685,plain,
    ( ~ sP1(X0_50,sK7,sK9,sK8)
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_3686,plain,
    ( sP1(X0_50,sK7,sK9,sK8) != iProver_top
    | r1_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3685])).

cnf(c_5,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_374,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | r1_orders_2(X0_49,X0_50,k10_lattice3(X0_49,X1_50,X0_50))
    | ~ m1_subset_1(k10_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1045,plain,
    ( sP0(X0_49,X0_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,X0_50,k10_lattice3(X0_49,X1_50,X0_50)) = iProver_top
    | m1_subset_1(k10_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_7746,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK9,k10_lattice3(sK7,sK8,sK9)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7729,c_1045])).

cnf(c_7750,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK9,sK10) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7746,c_7729])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_orders_2(X0,X2,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_373,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | r1_orders_2(X0_49,X1_50,k10_lattice3(X0_49,X1_50,X0_50))
    | ~ m1_subset_1(k10_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1046,plain,
    ( sP0(X0_49,X0_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,X1_50,k10_lattice3(X0_49,X1_50,X0_50)) = iProver_top
    | m1_subset_1(k10_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_7745,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK8,k10_lattice3(sK7,sK8,sK9)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7729,c_1046])).

cnf(c_7757,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK8,sK10) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7745,c_7729])).

cnf(c_8951,plain,
    ( sP1(sK10,sK7,sK9,sK8) != iProver_top
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK6(sK10,sK7,sK9,sK8)) = iProver_top
    | r1_orders_2(sK7,sK9,sK10) != iProver_top
    | r1_orders_2(sK7,sK8,sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8949])).

cnf(c_10473,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | sP1(X0_50,sK7,sK9,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8949,c_38,c_37,c_36,c_35,c_34,c_43,c_481,c_1571,c_1677,c_1678,c_2901,c_3686,c_5973,c_7727,c_7750,c_7757,c_8951])).

cnf(c_10474,plain,
    ( sP1(X0_50,sK7,sK9,sK8) != iProver_top
    | sP0(sK7,sK9,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_10473])).

cnf(c_10475,plain,
    ( ~ sP1(X0_50,sK7,sK9,sK8)
    | ~ sP0(sK7,sK9,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10474])).

cnf(c_10477,plain,
    ( ~ sP1(sK10,sK7,sK9,sK8)
    | ~ sP0(sK7,sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_10475])).

cnf(c_4538,plain,
    ( sP0(sK7,sK9,X0_50)
    | r1_orders_2(sK7,X0_50,sK3(sK7,X0_50,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ r1_orders_2(sK7,X0_50,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ r1_orders_2(sK7,sK9,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_8398,plain,
    ( sP0(sK7,sK9,sK8)
    | ~ r1_orders_2(sK7,sK9,sK5(sK7,k2_tarski(sK8,sK9)))
    | r1_orders_2(sK7,sK8,sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ r1_orders_2(sK7,sK8,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_4538])).

cnf(c_4564,plain,
    ( sP0(sK7,sK9,X0_50)
    | ~ r1_orders_2(sK7,X0_50,sK5(sK7,k2_tarski(sK8,sK9)))
    | r1_orders_2(sK7,sK9,sK3(sK7,X0_50,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ r1_orders_2(sK7,sK9,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_8278,plain,
    ( sP0(sK7,sK9,sK8)
    | r1_orders_2(sK7,sK9,sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))))
    | ~ r1_orders_2(sK7,sK9,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ r1_orders_2(sK7,sK8,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_4564])).

cnf(c_4408,plain,
    ( sP0(sK7,sK9,X0_50)
    | ~ r1_orders_2(sK7,X0_50,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ r1_orders_2(sK7,sK9,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | m1_subset_1(sK3(sK7,X0_50,sK9,sK5(sK7,k2_tarski(sK8,sK9))),u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_8254,plain,
    ( sP0(sK7,sK9,sK8)
    | ~ r1_orders_2(sK7,sK9,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ r1_orders_2(sK7,sK8,sK5(sK7,k2_tarski(sK8,sK9)))
    | m1_subset_1(sK3(sK7,sK8,sK9,sK5(sK7,k2_tarski(sK8,sK9))),u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_4408])).

cnf(c_1780,plain,
    ( ~ r2_lattice3(sK7,k2_tarski(sK8,sK9),sK5(sK7,k2_tarski(sK8,sK9)))
    | r1_orders_2(sK7,sK9,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_1781,plain,
    ( ~ r2_lattice3(sK7,k2_tarski(sK8,sK9),sK5(sK7,k2_tarski(sK8,sK9)))
    | r1_orders_2(sK7,sK8,sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_16,plain,
    ( r2_lattice3(X0,X1,sK5(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_363,plain,
    ( r2_lattice3(X0_49,X0_52,sK5(X0_49,X0_52))
    | ~ r1_yellow_0(X0_49,X0_52)
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1705,plain,
    ( r2_lattice3(sK7,k2_tarski(sK8,sK9),sK5(sK7,k2_tarski(sK8,sK9)))
    | ~ r1_yellow_0(sK7,k2_tarski(sK8,sK9))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_17,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_362,plain,
    ( ~ r1_yellow_0(X0_49,X0_52)
    | m1_subset_1(sK5(X0_49,X0_52),u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49)
    | ~ v5_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1706,plain,
    ( ~ r1_yellow_0(sK7,k2_tarski(sK8,sK9))
    | m1_subset_1(sK5(sK7,k2_tarski(sK8,sK9)),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v5_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37286,c_29596,c_25662,c_18142,c_10477,c_8398,c_8278,c_8254,c_1780,c_1781,c_1705,c_1706,c_1568,c_35,c_36,c_37,c_38])).


%------------------------------------------------------------------------------
