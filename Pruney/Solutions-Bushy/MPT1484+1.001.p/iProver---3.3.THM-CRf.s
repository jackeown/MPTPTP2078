%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1484+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:43 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 655 expanded)
%              Number of clauses        :  109 ( 187 expanded)
%              Number of leaves         :   19 ( 191 expanded)
%              Depth                    :   20
%              Number of atoms          : 1051 (4251 expanded)
%              Number of equality atoms :  193 ( 644 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,plain,(
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

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X1,X4)
          & r1_orders_2(X0,X2,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK1(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK1(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k10_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,X3,sK1(X0,X1,X2,X3))
                & r1_orders_2(X0,X1,sK1(X0,X1,X2,X3))
                & r1_orders_2(X0,X2,sK1(X0,X1,X2,X3))
                & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,sK1(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,X1,sK1(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
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

fof(f12,plain,(
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
    inference(rectify,[],[f2])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f34,plain,(
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
    inference(definition_folding,[],[f16,f33])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK2(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK2(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK2(X0,X1,X2,X3))
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,X3,sK2(X0,X1,X2,X3))
                    & r1_orders_2(X0,X2,sK2(X0,X1,X2,X3))
                    & r1_orders_2(X0,X1,sK2(X0,X1,X2,X3))
                    & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f40])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | r1_orders_2(X0,X2,sK2(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k13_lattice3(X0,k12_lattice3(X0,X1,sK6),sK6) != sK6
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k13_lattice3(X0,k12_lattice3(X0,sK5,X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(sK4,k12_lattice3(sK4,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) != sK6
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f50,f49,f48])).

fof(f79,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,sK2(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) != sK6 ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X3,sK1(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3281,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | ~ r1_orders_2(X0_49,X2_50,sK1(X0_49,X0_50,X1_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k10_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_7035,plain,
    ( ~ sP0(sK4,X0_50,k11_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,X1_50)
    | ~ r1_orders_2(sK4,X1_50,sK1(sK4,X0_50,k11_lattice3(sK4,sK5,sK6),X1_50))
    | ~ r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),X1_50)
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50) = X1_50 ),
    inference(instantiation,[status(thm)],[c_3281])).

cnf(c_7051,plain,
    ( k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50) = X1_50
    | sP0(sK4,X0_50,k11_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK4,X1_50,sK1(sK4,X0_50,k11_lattice3(sK4,sK5,sK6),X1_50)) != iProver_top
    | r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7035])).

cnf(c_7053,plain,
    ( k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6) = sK6
    | sP0(sK4,sK6,k11_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK1(sK4,sK6,k11_lattice3(sK4,sK5,sK6),sK6)) != iProver_top
    | r1_orders_2(sK4,sK6,sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7051])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,sK1(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3280,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X0_50,X2_50)
    | ~ r1_orders_2(X0_49,X1_50,X2_50)
    | r1_orders_2(X0_49,X0_50,sK1(X0_49,X0_50,X1_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k10_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_7036,plain,
    ( ~ sP0(sK4,X0_50,k11_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,X1_50)
    | r1_orders_2(sK4,X0_50,sK1(sK4,X0_50,k11_lattice3(sK4,sK5,sK6),X1_50))
    | ~ r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),X1_50)
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50) = X1_50 ),
    inference(instantiation,[status(thm)],[c_3280])).

cnf(c_7047,plain,
    ( k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50) = X1_50
    | sP0(sK4,X0_50,k11_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK4,X0_50,sK1(sK4,X0_50,k11_lattice3(sK4,sK5,sK6),X1_50)) = iProver_top
    | r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7036])).

cnf(c_7049,plain,
    ( k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6) = sK6
    | sP0(sK4,sK6,k11_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK1(sK4,sK6,k11_lattice3(sK4,sK5,sK6),sK6)) = iProver_top
    | r1_orders_2(sK4,sK6,sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7047])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,sK2(X0,X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_884,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,sK2(X0,X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_32])).

cnf(c_885,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X0,X2)
    | ~ r1_orders_2(sK4,X1,X2)
    | r1_orders_2(sK4,X0,sK2(sK4,X1,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_887,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_orders_2(sK4,X0,sK2(sK4,X1,X0,X2))
    | ~ r1_orders_2(sK4,X1,X2)
    | ~ r1_orders_2(sK4,X0,X2)
    | sP0(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_885,c_29])).

cnf(c_888,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X1,X2)
    | ~ r1_orders_2(sK4,X0,X2)
    | r1_orders_2(sK4,X0,sK2(sK4,X1,X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_887])).

cnf(c_3261,plain,
    ( sP0(sK4,X0_50,X1_50)
    | ~ r1_orders_2(sK4,X0_50,X2_50)
    | ~ r1_orders_2(sK4,X1_50,X2_50)
    | r1_orders_2(sK4,X0_50,sK2(sK4,X1_50,X0_50,X2_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_888])).

cnf(c_6833,plain,
    ( sP0(sK4,X0_50,k11_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,X1_50)
    | r1_orders_2(sK4,X0_50,sK2(sK4,k11_lattice3(sK4,sK5,sK6),X0_50,X1_50))
    | ~ r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | ~ m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3261])).

cnf(c_6844,plain,
    ( sP0(sK4,X0_50,k11_lattice3(sK4,sK5,sK6)) = iProver_top
    | r1_orders_2(sK4,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK4,X0_50,sK2(sK4,k11_lattice3(sK4,sK5,sK6),X0_50,X1_50)) = iProver_top
    | r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),X1_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6833])).

cnf(c_6846,plain,
    ( sP0(sK4,sK6,k11_lattice3(sK4,sK5,sK6)) = iProver_top
    | r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK2(sK4,k11_lattice3(sK4,sK5,sK6),sK6,sK6)) = iProver_top
    | r1_orders_2(sK4,sK6,sK6) != iProver_top
    | m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6844])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X3,sK2(X0,X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_913,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X3,sK2(X0,X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_32])).

cnf(c_914,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X0,X2)
    | ~ r1_orders_2(sK4,X1,X2)
    | ~ r1_orders_2(sK4,X2,sK2(sK4,X1,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_913])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_orders_2(sK4,X2,sK2(sK4,X1,X0,X2))
    | ~ r1_orders_2(sK4,X1,X2)
    | ~ r1_orders_2(sK4,X0,X2)
    | sP0(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_914,c_29])).

cnf(c_919,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X1,X2)
    | ~ r1_orders_2(sK4,X0,X2)
    | ~ r1_orders_2(sK4,X2,sK2(sK4,X1,X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_918])).

cnf(c_3260,plain,
    ( sP0(sK4,X0_50,X1_50)
    | ~ r1_orders_2(sK4,X0_50,X2_50)
    | ~ r1_orders_2(sK4,X1_50,X2_50)
    | ~ r1_orders_2(sK4,X2_50,sK2(sK4,X1_50,X0_50,X2_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_919])).

cnf(c_6834,plain,
    ( sP0(sK4,X0_50,k11_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,X1_50)
    | ~ r1_orders_2(sK4,X1_50,sK2(sK4,k11_lattice3(sK4,sK5,sK6),X0_50,X1_50))
    | ~ r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | ~ m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3260])).

cnf(c_6840,plain,
    ( sP0(sK4,X0_50,k11_lattice3(sK4,sK5,sK6)) = iProver_top
    | r1_orders_2(sK4,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK4,X1_50,sK2(sK4,k11_lattice3(sK4,sK5,sK6),X0_50,X1_50)) != iProver_top
    | r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),X1_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6834])).

cnf(c_6842,plain,
    ( sP0(sK4,sK6,k11_lattice3(sK4,sK5,sK6)) = iProver_top
    | r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK2(sK4,k11_lattice3(sK4,sK5,sK6),sK6,sK6)) != iProver_top
    | r1_orders_2(sK4,sK6,sK6) != iProver_top
    | m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6840])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_978,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k11_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_978])).

cnf(c_19,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_193,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_0])).

cnf(c_194,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_30,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_674,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_30])).

cnf(c_675,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k11_lattice3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_679,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k11_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_32,c_29])).

cnf(c_680,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k11_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_998,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_979,c_680])).

cnf(c_3256,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,X0_50,X1_50),X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_998])).

cnf(c_6068,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3256])).

cnf(c_6071,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,sK5,sK6),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6068])).

cnf(c_3287,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_6059,plain,
    ( X0_50 != X1_50
    | X0_50 = k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X2_50)
    | k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X2_50) != X1_50 ),
    inference(instantiation,[status(thm)],[c_3287])).

cnf(c_6060,plain,
    ( k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6) != sK6
    | sK6 = k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_6059])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k13_lattice3(sK4,X0,X1) = k10_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k13_lattice3(sK4,X0,X1) = k10_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_32,c_29])).

cnf(c_3271,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | k13_lattice3(sK4,X0_50,X1_50) = k10_lattice3(sK4,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_5148,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50) = k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50) ),
    inference(instantiation,[status(thm)],[c_3271])).

cnf(c_5150,plain,
    ( ~ m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6) = k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_5148])).

cnf(c_4203,plain,
    ( k13_lattice3(sK4,X0_50,X1_50) != X2_50
    | sK6 != X2_50
    | sK6 = k13_lattice3(sK4,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_3287])).

cnf(c_4365,plain,
    ( k13_lattice3(sK4,X0_50,X1_50) != k10_lattice3(sK4,X0_50,X1_50)
    | sK6 = k13_lattice3(sK4,X0_50,X1_50)
    | sK6 != k10_lattice3(sK4,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_4203])).

cnf(c_4954,plain,
    ( k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50) != k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50)
    | sK6 = k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50)
    | sK6 != k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50) ),
    inference(instantiation,[status(thm)],[c_4365])).

cnf(c_4955,plain,
    ( k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6) != k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6)
    | sK6 = k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6)
    | sK6 != k10_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_4954])).

cnf(c_3259,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | m1_subset_1(k11_lattice3(sK4,X0_50,X1_50),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_979])).

cnf(c_4702,plain,
    ( m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3259])).

cnf(c_4703,plain,
    ( m1_subset_1(k11_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4702])).

cnf(c_4125,plain,
    ( X0_50 != X1_50
    | k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) != X1_50
    | k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) = X0_50 ),
    inference(instantiation,[status(thm)],[c_3287])).

cnf(c_4247,plain,
    ( X0_50 != k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X1_50)
    | k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) = X0_50
    | k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) != k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X1_50) ),
    inference(instantiation,[status(thm)],[c_4125])).

cnf(c_4248,plain,
    ( k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) != k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6)
    | k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) = sK6
    | sK6 != k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_4247])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k12_lattice3(sK4,X0,X1) = k11_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k12_lattice3(sK4,X0,X1) = k11_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_32,c_29])).

cnf(c_3265,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | k12_lattice3(sK4,X0_50,X1_50) = k11_lattice3(sK4,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_723])).

cnf(c_4206,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k12_lattice3(sK4,sK5,sK6) = k11_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3265])).

cnf(c_3291,plain,
    ( X0_50 != X1_50
    | X2_50 != X3_50
    | k13_lattice3(X0_49,X0_50,X2_50) = k13_lattice3(X0_49,X1_50,X3_50) ),
    theory(equality)).

cnf(c_4127,plain,
    ( k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) = k13_lattice3(sK4,X0_50,X1_50)
    | k12_lattice3(sK4,sK5,sK6) != X0_50
    | sK6 != X1_50 ),
    inference(instantiation,[status(thm)],[c_3291])).

cnf(c_4205,plain,
    ( k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) = k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),X0_50)
    | k12_lattice3(sK4,sK5,sK6) != k11_lattice3(sK4,sK5,sK6)
    | sK6 != X0_50 ),
    inference(instantiation,[status(thm)],[c_4127])).

cnf(c_4207,plain,
    ( k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) = k13_lattice3(sK4,k11_lattice3(sK4,sK5,sK6),sK6)
    | k12_lattice3(sK4,sK5,sK6) != k11_lattice3(sK4,sK5,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4205])).

cnf(c_25,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_414,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_415,plain,
    ( r3_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_105,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_419,plain,
    ( r3_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_30,c_29,c_105])).

cnf(c_420,plain,
    ( r3_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_24,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_435,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_436,plain,
    ( ~ r3_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_440,plain,
    ( ~ r3_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_30,c_29,c_105])).

cnf(c_441,plain,
    ( ~ r3_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_494,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | X0 != X2
    | X1 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_420,c_441])).

cnf(c_495,plain,
    ( r1_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_3270,plain,
    ( r1_orders_2(sK4,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_3282,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3270])).

cnf(c_3324,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3282])).

cnf(c_3326,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3324])).

cnf(c_3283,plain,
    ( r1_orders_2(sK4,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_3270])).

cnf(c_3321,plain,
    ( r1_orders_2(sK4,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3283])).

cnf(c_3323,plain,
    ( r1_orders_2(sK4,sK6,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3321])).

cnf(c_3284,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3270])).

cnf(c_3320,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3284])).

cnf(c_26,negated_conjecture,
    ( k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) != sK6 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3274,negated_conjecture,
    ( k13_lattice3(sK4,k12_lattice3(sK4,sK5,sK6),sK6) != sK6 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3286,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_3297,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3286])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7053,c_7049,c_6846,c_6842,c_6071,c_6060,c_5150,c_4955,c_4703,c_4702,c_4248,c_4206,c_4207,c_3326,c_3323,c_3320,c_3274,c_3297,c_40,c_27,c_39,c_28])).


%------------------------------------------------------------------------------
