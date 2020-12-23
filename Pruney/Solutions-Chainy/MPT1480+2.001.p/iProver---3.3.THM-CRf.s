%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:00 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  167 (2801 expanded)
%              Number of clauses        :  115 ( 777 expanded)
%              Number of leaves         :   14 ( 843 expanded)
%              Depth                    :   36
%              Number of atoms          : 1069 (19296 expanded)
%              Number of equality atoms :  273 (3095 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k10_lattice3(X0,X1,sK9) != k10_lattice3(X0,sK9,X1)
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k10_lattice3(X0,X2,sK8) != k10_lattice3(X0,sK8,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(sK7,X1,X2) != k10_lattice3(sK7,X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK7)) )
          & m1_subset_1(X1,u1_struct_0(sK7)) )
      & l1_orders_2(sK7)
      & v1_lattice3(sK7)
      & v5_orders_2(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k10_lattice3(sK7,sK8,sK9) != k10_lattice3(sK7,sK9,sK8)
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l1_orders_2(sK7)
    & v1_lattice3(sK7)
    & v5_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f13,f32,f31,f30])).

fof(f58,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X3,X4)
                      | ~ r1_orders_2(X0,X2,X4)
                      | ~ r1_orders_2(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( r1_orders_2(X0,X7,X8)
                        | ~ r1_orders_2(X0,X6,X8)
                        | ~ r1_orders_2(X0,X5,X8)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f23,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X7,X8)
              | ~ r1_orders_2(X0,X6,X8)
              | ~ r1_orders_2(X0,X5,X8)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,sK5(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK5(X0,X5,X6))
        & r1_orders_2(X0,X5,sK5(X0,X5,X6))
        & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK4(X0,X3))
        & r1_orders_2(X0,X2,sK4(X0,X3))
        & r1_orders_2(X0,X1,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r1_orders_2(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,sK3(X0),X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK3(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r1_orders_2(X0,sK2(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK2(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,X3,sK4(X0,X3))
                & r1_orders_2(X0,sK3(X0),sK4(X0,X3))
                & r1_orders_2(X0,sK2(X0),sK4(X0,X3))
                & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK3(X0),X3)
              | ~ r1_orders_2(X0,sK2(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK3(X0),u1_struct_0(X0))
          & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,sK5(X0,X5,X6),X8)
                      | ~ r1_orders_2(X0,X6,X8)
                      | ~ r1_orders_2(X0,X5,X8)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X6,sK5(X0,X5,X6))
                  & r1_orders_2(X0,X5,sK5(X0,X5,X6))
                  & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f23,f22,f21,f20])).

fof(f37,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK5(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
                        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    v1_lattice3(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK5(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X2,X4)
                            & r1_orders_2(X0,X1,X4) )
                         => r1_orders_2(X0,X3,X4) ) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f9,f15,f14])).

fof(f47,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK5(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f60,plain,(
    k10_lattice3(sK7,sK8,sK9) != k10_lattice3(sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2408,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2769,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2408])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2409,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2768,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2411,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | m1_subset_1(sK5(X0_46,X1_47,X0_47),u1_struct_0(X0_46))
    | ~ sP0(X0_46) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2767,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(sK5(X0_46,X0_47,X1_47),u1_struct_0(X0_46)) = iProver_top
    | sP0(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2413,plain,
    ( r1_orders_2(X0_46,X0_47,sK5(X0_46,X1_47,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ sP0(X0_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2765,plain,
    ( r1_orders_2(X0_46,X0_47,sK5(X0_46,X1_47,X0_47)) = iProver_top
    | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | sP0(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2413])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_171,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_0])).

cnf(c_172,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_419,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_26])).

cnf(c_420,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | r1_orders_2(sK7,X0,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_25,negated_conjecture,
    ( v1_lattice3(sK7) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_422,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | r1_orders_2(sK7,X0,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_25,c_24])).

cnf(c_423,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | r1_orders_2(sK7,X0,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_2405,plain,
    ( ~ r1_orders_2(sK7,X0_47,X1_47)
    | ~ r1_orders_2(sK7,X2_47,X1_47)
    | r1_orders_2(sK7,X0_47,sK6(sK7,X0_47,X2_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0_47,X2_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_2772,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = X2_47
    | r1_orders_2(sK7,X0_47,X2_47) != iProver_top
    | r1_orders_2(sK7,X1_47,X2_47) != iProver_top
    | r1_orders_2(sK7,X0_47,sK6(sK7,X0_47,X1_47,X2_47)) = iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2405])).

cnf(c_15,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_178,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_0])).

cnf(c_179,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_386,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_26])).

cnf(c_387,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | r1_orders_2(sK7,X2,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_391,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | r1_orders_2(sK7,X2,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_25,c_24])).

cnf(c_392,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | r1_orders_2(sK7,X2,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_2406,plain,
    ( ~ r1_orders_2(sK7,X0_47,X1_47)
    | ~ r1_orders_2(sK7,X2_47,X1_47)
    | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X2_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0_47,X2_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_2771,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = X2_47
    | r1_orders_2(sK7,X0_47,X2_47) != iProver_top
    | r1_orders_2(sK7,X1_47,X2_47) != iProver_top
    | r1_orders_2(sK7,X1_47,sK6(sK7,X0_47,X1_47,X2_47)) = iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2406])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK5(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2414,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | ~ r1_orders_2(X0_46,X2_47,X1_47)
    | r1_orders_2(X0_46,sK5(X0_46,X2_47,X0_47),X1_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
    | ~ sP0(X0_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2764,plain,
    ( r1_orders_2(X0_46,X0_47,X1_47) != iProver_top
    | r1_orders_2(X0_46,X2_47,X1_47) != iProver_top
    | r1_orders_2(X0_46,sK5(X0_46,X2_47,X0_47),X1_47) = iProver_top
    | m1_subset_1(X2_47,u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | sP0(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_183,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_0])).

cnf(c_184,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_353,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_26])).

cnf(c_354,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X1,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_358,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X1,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_25,c_24])).

cnf(c_359,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X1,sK6(sK7,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_2407,plain,
    ( ~ r1_orders_2(sK7,X0_47,X1_47)
    | ~ r1_orders_2(sK7,X2_47,X1_47)
    | ~ r1_orders_2(sK7,X1_47,sK6(sK7,X0_47,X2_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | k10_lattice3(sK7,X0_47,X2_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_2770,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = X2_47
    | r1_orders_2(sK7,X0_47,X2_47) != iProver_top
    | r1_orders_2(sK7,X1_47,X2_47) != iProver_top
    | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,X2_47)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2407])).

cnf(c_4231,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
    | r1_orders_2(sK7,X3_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
    | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
    | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X3_47)) != iProver_top
    | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X3_47)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2764,c_2770])).

cnf(c_28,plain,
    ( v1_lattice3(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( l1_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( sP1(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_49,plain,
    ( sP1(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_51,plain,
    ( sP1(sK7) = iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_2,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_80,plain,
    ( sP1(X0) != iProver_top
    | sP0(X0) = iProver_top
    | v1_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_82,plain,
    ( sP1(sK7) != iProver_top
    | sP0(sK7) = iProver_top
    | v1_lattice3(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_17,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_164,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_0])).

cnf(c_165,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_448,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_165,c_26])).

cnf(c_449,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0,X2,X1),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_453,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0,X2,X1),u1_struct_0(sK7))
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_25,c_24])).

cnf(c_454,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0,X2,X1),u1_struct_0(sK7))
    | k10_lattice3(sK7,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_2404,plain,
    ( ~ r1_orders_2(sK7,X0_47,X1_47)
    | ~ r1_orders_2(sK7,X2_47,X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0_47,X2_47,X1_47),u1_struct_0(sK7))
    | k10_lattice3(sK7,X0_47,X2_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_3997,plain,
    ( ~ r1_orders_2(sK7,X0_47,sK5(sK7,X1_47,X2_47))
    | ~ r1_orders_2(sK7,X3_47,sK5(sK7,X1_47,X2_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X3_47,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0_47,X3_47,sK5(sK7,X1_47,X2_47)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,X1_47,X2_47),u1_struct_0(sK7))
    | k10_lattice3(sK7,X0_47,X3_47) = sK5(sK7,X1_47,X2_47) ),
    inference(instantiation,[status(thm)],[c_2404])).

cnf(c_4003,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
    | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X3_47)) != iProver_top
    | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X3_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3997])).

cnf(c_4459,plain,
    ( m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top
    | k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
    | r1_orders_2(sK7,X3_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
    | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
    | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X3_47)) != iProver_top
    | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X3_47)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4231,c_28,c_29,c_51,c_82,c_4003])).

cnf(c_4460,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
    | r1_orders_2(sK7,X3_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
    | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
    | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X3_47)) != iProver_top
    | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X3_47)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4459])).

cnf(c_4476,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X1_47)
    | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X1_47))) != iProver_top
    | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X1_47)) != iProver_top
    | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X1_47)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2771,c_4460])).

cnf(c_4556,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | r1_orders_2(sK7,X0_47,sK5(sK7,X0_47,X1_47)) != iProver_top
    | r1_orders_2(sK7,X1_47,sK5(sK7,X0_47,X1_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2772,c_4476])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2412,plain,
    ( r1_orders_2(X0_46,X0_47,sK5(X0_46,X0_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ sP0(X0_46) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3014,plain,
    ( r1_orders_2(sK7,X0_47,sK5(sK7,X0_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_2412])).

cnf(c_3020,plain,
    ( r1_orders_2(sK7,X0_47,sK5(sK7,X0_47,X1_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3014])).

cnf(c_4774,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | r1_orders_2(sK7,X1_47,sK5(sK7,X0_47,X1_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4556,c_28,c_29,c_51,c_82,c_3020])).

cnf(c_4784,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2765,c_4774])).

cnf(c_7265,plain,
    ( m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4784,c_28,c_29,c_51,c_82])).

cnf(c_7266,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7265])).

cnf(c_7273,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2767,c_7266])).

cnf(c_7374,plain,
    ( m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7273,c_28,c_29,c_51,c_82])).

cnf(c_7375,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7374])).

cnf(c_7381,plain,
    ( k10_lattice3(sK7,sK9,X0_47) = sK5(sK7,sK9,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2768,c_7375])).

cnf(c_7434,plain,
    ( k10_lattice3(sK7,sK9,sK8) = sK5(sK7,sK9,sK8) ),
    inference(superposition,[status(thm)],[c_2769,c_7381])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_145,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_0])).

cnf(c_146,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_538,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_146,c_26])).

cnf(c_539,plain,
    ( r1_orders_2(sK7,X0,k10_lattice3(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_lattice3(sK7,X0,X1),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v1_lattice3(sK7) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_541,plain,
    ( r1_orders_2(sK7,X0,k10_lattice3(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_lattice3(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_25,c_24])).

cnf(c_2401,plain,
    ( r1_orders_2(sK7,X0_47,k10_lattice3(sK7,X0_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_lattice3(sK7,X0_47,X1_47),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_541])).

cnf(c_2776,plain,
    ( r1_orders_2(sK7,X0_47,k10_lattice3(sK7,X0_47,X1_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k10_lattice3(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2401])).

cnf(c_7624,plain,
    ( r1_orders_2(sK7,sK9,k10_lattice3(sK7,sK9,sK8)) = iProver_top
    | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7434,c_2776])).

cnf(c_7655,plain,
    ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,sK8)) = iProver_top
    | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7624,c_7434])).

cnf(c_30,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3376,plain,
    ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_3014])).

cnf(c_3377,plain,
    ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,X0_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3376])).

cnf(c_3379,plain,
    ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3377])).

cnf(c_8122,plain,
    ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7655,c_28,c_29,c_30,c_31,c_51,c_82,c_3379])).

cnf(c_4477,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X0_47)
    | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X0_47))) != iProver_top
    | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X0_47)) != iProver_top
    | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X0_47)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2772,c_4460])).

cnf(c_4961,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X1_47,X0_47)
    | r1_orders_2(sK7,X0_47,sK5(sK7,X1_47,X0_47)) != iProver_top
    | r1_orders_2(sK7,X1_47,sK5(sK7,X1_47,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X1_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2771,c_4477])).

cnf(c_3040,plain,
    ( r1_orders_2(sK7,X0_47,sK5(sK7,X1_47,X0_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_2413])).

cnf(c_3046,plain,
    ( r1_orders_2(sK7,X0_47,sK5(sK7,X1_47,X0_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3040])).

cnf(c_5017,plain,
    ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X1_47,X0_47)
    | r1_orders_2(sK7,X1_47,sK5(sK7,X1_47,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X1_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4961,c_28,c_29,c_51,c_82,c_3046])).

cnf(c_8130,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK5(sK7,sK9,sK8)
    | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8122,c_5017])).

cnf(c_7382,plain,
    ( k10_lattice3(sK7,sK8,X0_47) = sK5(sK7,sK8,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2769,c_7375])).

cnf(c_7805,plain,
    ( k10_lattice3(sK7,sK8,sK9) = sK5(sK7,sK8,sK9) ),
    inference(superposition,[status(thm)],[c_2768,c_7382])).

cnf(c_8135,plain,
    ( sK5(sK7,sK8,sK9) = sK5(sK7,sK9,sK8)
    | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8130,c_7805])).

cnf(c_21,negated_conjecture,
    ( k10_lattice3(sK7,sK8,sK9) != k10_lattice3(sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2410,negated_conjecture,
    ( k10_lattice3(sK7,sK8,sK9) != k10_lattice3(sK7,sK9,sK8) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_7623,plain,
    ( k10_lattice3(sK7,sK8,sK9) != sK5(sK7,sK9,sK8) ),
    inference(demodulation,[status(thm)],[c_7434,c_2410])).

cnf(c_7841,plain,
    ( sK5(sK7,sK8,sK9) != sK5(sK7,sK9,sK8) ),
    inference(demodulation,[status(thm)],[c_7805,c_7623])).

cnf(c_5126,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,sK9,X0_47),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_2411])).

cnf(c_5127,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,sK9,X0_47),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5126])).

cnf(c_5129,plain,
    ( m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5127])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8135,c_7841,c_5129,c_82,c_51,c_31,c_30,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.35/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/0.99  
% 3.35/0.99  ------  iProver source info
% 3.35/0.99  
% 3.35/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.35/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/0.99  git: non_committed_changes: false
% 3.35/0.99  git: last_make_outside_of_git: false
% 3.35/0.99  
% 3.35/0.99  ------ 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options
% 3.35/0.99  
% 3.35/0.99  --out_options                           all
% 3.35/0.99  --tptp_safe_out                         true
% 3.35/0.99  --problem_path                          ""
% 3.35/0.99  --include_path                          ""
% 3.35/0.99  --clausifier                            res/vclausify_rel
% 3.35/0.99  --clausifier_options                    --mode clausify
% 3.35/0.99  --stdin                                 false
% 3.35/0.99  --stats_out                             all
% 3.35/0.99  
% 3.35/0.99  ------ General Options
% 3.35/0.99  
% 3.35/0.99  --fof                                   false
% 3.35/0.99  --time_out_real                         305.
% 3.35/0.99  --time_out_virtual                      -1.
% 3.35/0.99  --symbol_type_check                     false
% 3.35/0.99  --clausify_out                          false
% 3.35/0.99  --sig_cnt_out                           false
% 3.35/0.99  --trig_cnt_out                          false
% 3.35/0.99  --trig_cnt_out_tolerance                1.
% 3.35/0.99  --trig_cnt_out_sk_spl                   false
% 3.35/0.99  --abstr_cl_out                          false
% 3.35/0.99  
% 3.35/0.99  ------ Global Options
% 3.35/0.99  
% 3.35/0.99  --schedule                              default
% 3.35/0.99  --add_important_lit                     false
% 3.35/0.99  --prop_solver_per_cl                    1000
% 3.35/0.99  --min_unsat_core                        false
% 3.35/0.99  --soft_assumptions                      false
% 3.35/0.99  --soft_lemma_size                       3
% 3.35/0.99  --prop_impl_unit_size                   0
% 3.35/0.99  --prop_impl_unit                        []
% 3.35/0.99  --share_sel_clauses                     true
% 3.35/0.99  --reset_solvers                         false
% 3.35/0.99  --bc_imp_inh                            [conj_cone]
% 3.35/0.99  --conj_cone_tolerance                   3.
% 3.35/0.99  --extra_neg_conj                        none
% 3.35/0.99  --large_theory_mode                     true
% 3.35/0.99  --prolific_symb_bound                   200
% 3.35/0.99  --lt_threshold                          2000
% 3.35/0.99  --clause_weak_htbl                      true
% 3.35/0.99  --gc_record_bc_elim                     false
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing Options
% 3.35/0.99  
% 3.35/0.99  --preprocessing_flag                    true
% 3.35/0.99  --time_out_prep_mult                    0.1
% 3.35/0.99  --splitting_mode                        input
% 3.35/0.99  --splitting_grd                         true
% 3.35/0.99  --splitting_cvd                         false
% 3.35/0.99  --splitting_cvd_svl                     false
% 3.35/0.99  --splitting_nvd                         32
% 3.35/0.99  --sub_typing                            true
% 3.35/0.99  --prep_gs_sim                           true
% 3.35/0.99  --prep_unflatten                        true
% 3.35/0.99  --prep_res_sim                          true
% 3.35/0.99  --prep_upred                            true
% 3.35/0.99  --prep_sem_filter                       exhaustive
% 3.35/0.99  --prep_sem_filter_out                   false
% 3.35/0.99  --pred_elim                             true
% 3.35/0.99  --res_sim_input                         true
% 3.35/0.99  --eq_ax_congr_red                       true
% 3.35/0.99  --pure_diseq_elim                       true
% 3.35/0.99  --brand_transform                       false
% 3.35/0.99  --non_eq_to_eq                          false
% 3.35/0.99  --prep_def_merge                        true
% 3.35/0.99  --prep_def_merge_prop_impl              false
% 3.35/0.99  --prep_def_merge_mbd                    true
% 3.35/0.99  --prep_def_merge_tr_red                 false
% 3.35/0.99  --prep_def_merge_tr_cl                  false
% 3.35/0.99  --smt_preprocessing                     true
% 3.35/0.99  --smt_ac_axioms                         fast
% 3.35/0.99  --preprocessed_out                      false
% 3.35/0.99  --preprocessed_stats                    false
% 3.35/0.99  
% 3.35/0.99  ------ Abstraction refinement Options
% 3.35/0.99  
% 3.35/0.99  --abstr_ref                             []
% 3.35/0.99  --abstr_ref_prep                        false
% 3.35/0.99  --abstr_ref_until_sat                   false
% 3.35/0.99  --abstr_ref_sig_restrict                funpre
% 3.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.99  --abstr_ref_under                       []
% 3.35/0.99  
% 3.35/0.99  ------ SAT Options
% 3.35/0.99  
% 3.35/0.99  --sat_mode                              false
% 3.35/0.99  --sat_fm_restart_options                ""
% 3.35/0.99  --sat_gr_def                            false
% 3.35/0.99  --sat_epr_types                         true
% 3.35/0.99  --sat_non_cyclic_types                  false
% 3.35/0.99  --sat_finite_models                     false
% 3.35/0.99  --sat_fm_lemmas                         false
% 3.35/0.99  --sat_fm_prep                           false
% 3.35/0.99  --sat_fm_uc_incr                        true
% 3.35/0.99  --sat_out_model                         small
% 3.35/0.99  --sat_out_clauses                       false
% 3.35/0.99  
% 3.35/0.99  ------ QBF Options
% 3.35/0.99  
% 3.35/0.99  --qbf_mode                              false
% 3.35/0.99  --qbf_elim_univ                         false
% 3.35/0.99  --qbf_dom_inst                          none
% 3.35/0.99  --qbf_dom_pre_inst                      false
% 3.35/0.99  --qbf_sk_in                             false
% 3.35/0.99  --qbf_pred_elim                         true
% 3.35/0.99  --qbf_split                             512
% 3.35/0.99  
% 3.35/0.99  ------ BMC1 Options
% 3.35/0.99  
% 3.35/0.99  --bmc1_incremental                      false
% 3.35/0.99  --bmc1_axioms                           reachable_all
% 3.35/0.99  --bmc1_min_bound                        0
% 3.35/0.99  --bmc1_max_bound                        -1
% 3.35/0.99  --bmc1_max_bound_default                -1
% 3.35/0.99  --bmc1_symbol_reachability              true
% 3.35/0.99  --bmc1_property_lemmas                  false
% 3.35/0.99  --bmc1_k_induction                      false
% 3.35/0.99  --bmc1_non_equiv_states                 false
% 3.35/0.99  --bmc1_deadlock                         false
% 3.35/0.99  --bmc1_ucm                              false
% 3.35/0.99  --bmc1_add_unsat_core                   none
% 3.35/0.99  --bmc1_unsat_core_children              false
% 3.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.99  --bmc1_out_stat                         full
% 3.35/0.99  --bmc1_ground_init                      false
% 3.35/0.99  --bmc1_pre_inst_next_state              false
% 3.35/0.99  --bmc1_pre_inst_state                   false
% 3.35/0.99  --bmc1_pre_inst_reach_state             false
% 3.35/0.99  --bmc1_out_unsat_core                   false
% 3.35/0.99  --bmc1_aig_witness_out                  false
% 3.35/0.99  --bmc1_verbose                          false
% 3.35/0.99  --bmc1_dump_clauses_tptp                false
% 3.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.99  --bmc1_dump_file                        -
% 3.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.99  --bmc1_ucm_extend_mode                  1
% 3.35/0.99  --bmc1_ucm_init_mode                    2
% 3.35/0.99  --bmc1_ucm_cone_mode                    none
% 3.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.99  --bmc1_ucm_relax_model                  4
% 3.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.99  --bmc1_ucm_layered_model                none
% 3.35/0.99  --bmc1_ucm_max_lemma_size               10
% 3.35/0.99  
% 3.35/0.99  ------ AIG Options
% 3.35/0.99  
% 3.35/0.99  --aig_mode                              false
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation Options
% 3.35/0.99  
% 3.35/0.99  --instantiation_flag                    true
% 3.35/0.99  --inst_sos_flag                         false
% 3.35/0.99  --inst_sos_phase                        true
% 3.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel_side                     num_symb
% 3.35/0.99  --inst_solver_per_active                1400
% 3.35/0.99  --inst_solver_calls_frac                1.
% 3.35/0.99  --inst_passive_queue_type               priority_queues
% 3.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.99  --inst_passive_queues_freq              [25;2]
% 3.35/0.99  --inst_dismatching                      true
% 3.35/0.99  --inst_eager_unprocessed_to_passive     true
% 3.35/0.99  --inst_prop_sim_given                   true
% 3.35/0.99  --inst_prop_sim_new                     false
% 3.35/0.99  --inst_subs_new                         false
% 3.35/0.99  --inst_eq_res_simp                      false
% 3.35/0.99  --inst_subs_given                       false
% 3.35/0.99  --inst_orphan_elimination               true
% 3.35/0.99  --inst_learning_loop_flag               true
% 3.35/0.99  --inst_learning_start                   3000
% 3.35/0.99  --inst_learning_factor                  2
% 3.35/0.99  --inst_start_prop_sim_after_learn       3
% 3.35/0.99  --inst_sel_renew                        solver
% 3.35/0.99  --inst_lit_activity_flag                true
% 3.35/0.99  --inst_restr_to_given                   false
% 3.35/0.99  --inst_activity_threshold               500
% 3.35/0.99  --inst_out_proof                        true
% 3.35/0.99  
% 3.35/0.99  ------ Resolution Options
% 3.35/0.99  
% 3.35/0.99  --resolution_flag                       true
% 3.35/0.99  --res_lit_sel                           adaptive
% 3.35/0.99  --res_lit_sel_side                      none
% 3.35/0.99  --res_ordering                          kbo
% 3.35/0.99  --res_to_prop_solver                    active
% 3.35/0.99  --res_prop_simpl_new                    false
% 3.35/0.99  --res_prop_simpl_given                  true
% 3.35/0.99  --res_passive_queue_type                priority_queues
% 3.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.99  --res_passive_queues_freq               [15;5]
% 3.35/0.99  --res_forward_subs                      full
% 3.35/0.99  --res_backward_subs                     full
% 3.35/0.99  --res_forward_subs_resolution           true
% 3.35/0.99  --res_backward_subs_resolution          true
% 3.35/0.99  --res_orphan_elimination                true
% 3.35/0.99  --res_time_limit                        2.
% 3.35/0.99  --res_out_proof                         true
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Options
% 3.35/0.99  
% 3.35/0.99  --superposition_flag                    true
% 3.35/0.99  --sup_passive_queue_type                priority_queues
% 3.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.99  --demod_completeness_check              fast
% 3.35/0.99  --demod_use_ground                      true
% 3.35/0.99  --sup_to_prop_solver                    passive
% 3.35/0.99  --sup_prop_simpl_new                    true
% 3.35/0.99  --sup_prop_simpl_given                  true
% 3.35/0.99  --sup_fun_splitting                     false
% 3.35/0.99  --sup_smt_interval                      50000
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Simplification Setup
% 3.35/0.99  
% 3.35/0.99  --sup_indices_passive                   []
% 3.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_full_bw                           [BwDemod]
% 3.35/0.99  --sup_immed_triv                        [TrivRules]
% 3.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_immed_bw_main                     []
% 3.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  
% 3.35/0.99  ------ Combination Options
% 3.35/0.99  
% 3.35/0.99  --comb_res_mult                         3
% 3.35/0.99  --comb_sup_mult                         2
% 3.35/0.99  --comb_inst_mult                        10
% 3.35/0.99  
% 3.35/0.99  ------ Debug Options
% 3.35/0.99  
% 3.35/0.99  --dbg_backtrace                         false
% 3.35/0.99  --dbg_dump_prop_clauses                 false
% 3.35/0.99  --dbg_dump_prop_clauses_file            -
% 3.35/0.99  --dbg_out_stat                          false
% 3.35/0.99  ------ Parsing...
% 3.35/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/0.99  ------ Proving...
% 3.35/0.99  ------ Problem Properties 
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  clauses                                 21
% 3.35/0.99  conjectures                             3
% 3.35/0.99  EPR                                     1
% 3.35/0.99  Horn                                    13
% 3.35/0.99  unary                                   4
% 3.35/0.99  binary                                  2
% 3.35/0.99  lits                                    90
% 3.35/0.99  lits eq                                 5
% 3.35/0.99  fd_pure                                 0
% 3.35/0.99  fd_pseudo                               0
% 3.35/0.99  fd_cond                                 0
% 3.35/0.99  fd_pseudo_cond                          4
% 3.35/0.99  AC symbols                              0
% 3.35/0.99  
% 3.35/0.99  ------ Schedule dynamic 5 is on 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  ------ 
% 3.35/0.99  Current options:
% 3.35/0.99  ------ 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options
% 3.35/0.99  
% 3.35/0.99  --out_options                           all
% 3.35/0.99  --tptp_safe_out                         true
% 3.35/0.99  --problem_path                          ""
% 3.35/0.99  --include_path                          ""
% 3.35/0.99  --clausifier                            res/vclausify_rel
% 3.35/0.99  --clausifier_options                    --mode clausify
% 3.35/0.99  --stdin                                 false
% 3.35/0.99  --stats_out                             all
% 3.35/0.99  
% 3.35/0.99  ------ General Options
% 3.35/0.99  
% 3.35/0.99  --fof                                   false
% 3.35/0.99  --time_out_real                         305.
% 3.35/0.99  --time_out_virtual                      -1.
% 3.35/0.99  --symbol_type_check                     false
% 3.35/0.99  --clausify_out                          false
% 3.35/0.99  --sig_cnt_out                           false
% 3.35/0.99  --trig_cnt_out                          false
% 3.35/0.99  --trig_cnt_out_tolerance                1.
% 3.35/0.99  --trig_cnt_out_sk_spl                   false
% 3.35/0.99  --abstr_cl_out                          false
% 3.35/0.99  
% 3.35/0.99  ------ Global Options
% 3.35/0.99  
% 3.35/0.99  --schedule                              default
% 3.35/0.99  --add_important_lit                     false
% 3.35/0.99  --prop_solver_per_cl                    1000
% 3.35/0.99  --min_unsat_core                        false
% 3.35/0.99  --soft_assumptions                      false
% 3.35/0.99  --soft_lemma_size                       3
% 3.35/0.99  --prop_impl_unit_size                   0
% 3.35/0.99  --prop_impl_unit                        []
% 3.35/0.99  --share_sel_clauses                     true
% 3.35/0.99  --reset_solvers                         false
% 3.35/0.99  --bc_imp_inh                            [conj_cone]
% 3.35/0.99  --conj_cone_tolerance                   3.
% 3.35/0.99  --extra_neg_conj                        none
% 3.35/0.99  --large_theory_mode                     true
% 3.35/0.99  --prolific_symb_bound                   200
% 3.35/0.99  --lt_threshold                          2000
% 3.35/0.99  --clause_weak_htbl                      true
% 3.35/0.99  --gc_record_bc_elim                     false
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing Options
% 3.35/0.99  
% 3.35/0.99  --preprocessing_flag                    true
% 3.35/0.99  --time_out_prep_mult                    0.1
% 3.35/0.99  --splitting_mode                        input
% 3.35/0.99  --splitting_grd                         true
% 3.35/0.99  --splitting_cvd                         false
% 3.35/0.99  --splitting_cvd_svl                     false
% 3.35/0.99  --splitting_nvd                         32
% 3.35/0.99  --sub_typing                            true
% 3.35/0.99  --prep_gs_sim                           true
% 3.35/0.99  --prep_unflatten                        true
% 3.35/0.99  --prep_res_sim                          true
% 3.35/0.99  --prep_upred                            true
% 3.35/0.99  --prep_sem_filter                       exhaustive
% 3.35/0.99  --prep_sem_filter_out                   false
% 3.35/0.99  --pred_elim                             true
% 3.35/0.99  --res_sim_input                         true
% 3.35/0.99  --eq_ax_congr_red                       true
% 3.35/0.99  --pure_diseq_elim                       true
% 3.35/0.99  --brand_transform                       false
% 3.35/0.99  --non_eq_to_eq                          false
% 3.35/0.99  --prep_def_merge                        true
% 3.35/0.99  --prep_def_merge_prop_impl              false
% 3.35/0.99  --prep_def_merge_mbd                    true
% 3.35/0.99  --prep_def_merge_tr_red                 false
% 3.35/0.99  --prep_def_merge_tr_cl                  false
% 3.35/0.99  --smt_preprocessing                     true
% 3.35/0.99  --smt_ac_axioms                         fast
% 3.35/0.99  --preprocessed_out                      false
% 3.35/0.99  --preprocessed_stats                    false
% 3.35/0.99  
% 3.35/0.99  ------ Abstraction refinement Options
% 3.35/0.99  
% 3.35/0.99  --abstr_ref                             []
% 3.35/0.99  --abstr_ref_prep                        false
% 3.35/0.99  --abstr_ref_until_sat                   false
% 3.35/0.99  --abstr_ref_sig_restrict                funpre
% 3.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.99  --abstr_ref_under                       []
% 3.35/0.99  
% 3.35/0.99  ------ SAT Options
% 3.35/0.99  
% 3.35/0.99  --sat_mode                              false
% 3.35/0.99  --sat_fm_restart_options                ""
% 3.35/0.99  --sat_gr_def                            false
% 3.35/0.99  --sat_epr_types                         true
% 3.35/0.99  --sat_non_cyclic_types                  false
% 3.35/0.99  --sat_finite_models                     false
% 3.35/0.99  --sat_fm_lemmas                         false
% 3.35/0.99  --sat_fm_prep                           false
% 3.35/0.99  --sat_fm_uc_incr                        true
% 3.35/0.99  --sat_out_model                         small
% 3.35/0.99  --sat_out_clauses                       false
% 3.35/0.99  
% 3.35/0.99  ------ QBF Options
% 3.35/0.99  
% 3.35/0.99  --qbf_mode                              false
% 3.35/0.99  --qbf_elim_univ                         false
% 3.35/0.99  --qbf_dom_inst                          none
% 3.35/0.99  --qbf_dom_pre_inst                      false
% 3.35/0.99  --qbf_sk_in                             false
% 3.35/0.99  --qbf_pred_elim                         true
% 3.35/0.99  --qbf_split                             512
% 3.35/0.99  
% 3.35/0.99  ------ BMC1 Options
% 3.35/0.99  
% 3.35/0.99  --bmc1_incremental                      false
% 3.35/0.99  --bmc1_axioms                           reachable_all
% 3.35/0.99  --bmc1_min_bound                        0
% 3.35/0.99  --bmc1_max_bound                        -1
% 3.35/0.99  --bmc1_max_bound_default                -1
% 3.35/0.99  --bmc1_symbol_reachability              true
% 3.35/0.99  --bmc1_property_lemmas                  false
% 3.35/0.99  --bmc1_k_induction                      false
% 3.35/0.99  --bmc1_non_equiv_states                 false
% 3.35/0.99  --bmc1_deadlock                         false
% 3.35/0.99  --bmc1_ucm                              false
% 3.35/0.99  --bmc1_add_unsat_core                   none
% 3.35/0.99  --bmc1_unsat_core_children              false
% 3.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.99  --bmc1_out_stat                         full
% 3.35/0.99  --bmc1_ground_init                      false
% 3.35/0.99  --bmc1_pre_inst_next_state              false
% 3.35/0.99  --bmc1_pre_inst_state                   false
% 3.35/0.99  --bmc1_pre_inst_reach_state             false
% 3.35/0.99  --bmc1_out_unsat_core                   false
% 3.35/0.99  --bmc1_aig_witness_out                  false
% 3.35/0.99  --bmc1_verbose                          false
% 3.35/0.99  --bmc1_dump_clauses_tptp                false
% 3.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.99  --bmc1_dump_file                        -
% 3.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.99  --bmc1_ucm_extend_mode                  1
% 3.35/0.99  --bmc1_ucm_init_mode                    2
% 3.35/0.99  --bmc1_ucm_cone_mode                    none
% 3.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.99  --bmc1_ucm_relax_model                  4
% 3.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.99  --bmc1_ucm_layered_model                none
% 3.35/0.99  --bmc1_ucm_max_lemma_size               10
% 3.35/0.99  
% 3.35/0.99  ------ AIG Options
% 3.35/0.99  
% 3.35/0.99  --aig_mode                              false
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation Options
% 3.35/0.99  
% 3.35/0.99  --instantiation_flag                    true
% 3.35/0.99  --inst_sos_flag                         false
% 3.35/0.99  --inst_sos_phase                        true
% 3.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel_side                     none
% 3.35/0.99  --inst_solver_per_active                1400
% 3.35/0.99  --inst_solver_calls_frac                1.
% 3.35/0.99  --inst_passive_queue_type               priority_queues
% 3.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.99  --inst_passive_queues_freq              [25;2]
% 3.35/0.99  --inst_dismatching                      true
% 3.35/0.99  --inst_eager_unprocessed_to_passive     true
% 3.35/0.99  --inst_prop_sim_given                   true
% 3.35/0.99  --inst_prop_sim_new                     false
% 3.35/0.99  --inst_subs_new                         false
% 3.35/0.99  --inst_eq_res_simp                      false
% 3.35/0.99  --inst_subs_given                       false
% 3.35/0.99  --inst_orphan_elimination               true
% 3.35/0.99  --inst_learning_loop_flag               true
% 3.35/0.99  --inst_learning_start                   3000
% 3.35/0.99  --inst_learning_factor                  2
% 3.35/0.99  --inst_start_prop_sim_after_learn       3
% 3.35/0.99  --inst_sel_renew                        solver
% 3.35/0.99  --inst_lit_activity_flag                true
% 3.35/0.99  --inst_restr_to_given                   false
% 3.35/0.99  --inst_activity_threshold               500
% 3.35/0.99  --inst_out_proof                        true
% 3.35/0.99  
% 3.35/0.99  ------ Resolution Options
% 3.35/0.99  
% 3.35/0.99  --resolution_flag                       false
% 3.35/0.99  --res_lit_sel                           adaptive
% 3.35/0.99  --res_lit_sel_side                      none
% 3.35/0.99  --res_ordering                          kbo
% 3.35/0.99  --res_to_prop_solver                    active
% 3.35/0.99  --res_prop_simpl_new                    false
% 3.35/0.99  --res_prop_simpl_given                  true
% 3.35/0.99  --res_passive_queue_type                priority_queues
% 3.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.99  --res_passive_queues_freq               [15;5]
% 3.35/0.99  --res_forward_subs                      full
% 3.35/0.99  --res_backward_subs                     full
% 3.35/0.99  --res_forward_subs_resolution           true
% 3.35/0.99  --res_backward_subs_resolution          true
% 3.35/0.99  --res_orphan_elimination                true
% 3.35/0.99  --res_time_limit                        2.
% 3.35/0.99  --res_out_proof                         true
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Options
% 3.35/0.99  
% 3.35/0.99  --superposition_flag                    true
% 3.35/0.99  --sup_passive_queue_type                priority_queues
% 3.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.99  --demod_completeness_check              fast
% 3.35/0.99  --demod_use_ground                      true
% 3.35/0.99  --sup_to_prop_solver                    passive
% 3.35/0.99  --sup_prop_simpl_new                    true
% 3.35/0.99  --sup_prop_simpl_given                  true
% 3.35/0.99  --sup_fun_splitting                     false
% 3.35/0.99  --sup_smt_interval                      50000
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Simplification Setup
% 3.35/0.99  
% 3.35/0.99  --sup_indices_passive                   []
% 3.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_full_bw                           [BwDemod]
% 3.35/0.99  --sup_immed_triv                        [TrivRules]
% 3.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_immed_bw_main                     []
% 3.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  
% 3.35/0.99  ------ Combination Options
% 3.35/0.99  
% 3.35/0.99  --comb_res_mult                         3
% 3.35/0.99  --comb_sup_mult                         2
% 3.35/0.99  --comb_inst_mult                        10
% 3.35/0.99  
% 3.35/0.99  ------ Debug Options
% 3.35/0.99  
% 3.35/0.99  --dbg_backtrace                         false
% 3.35/0.99  --dbg_dump_prop_clauses                 false
% 3.35/0.99  --dbg_dump_prop_clauses_file            -
% 3.35/0.99  --dbg_out_stat                          false
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  ------ Proving...
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS status Theorem for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  fof(f4,conjecture,(
% 3.35/0.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f5,negated_conjecture,(
% 3.35/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 3.35/0.99    inference(negated_conjecture,[],[f4])).
% 3.35/0.99  
% 3.35/0.99  fof(f12,plain,(
% 3.35/0.99    ? [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f5])).
% 3.35/0.99  
% 3.35/0.99  fof(f13,plain,(
% 3.35/0.99    ? [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0))),
% 3.35/0.99    inference(flattening,[],[f12])).
% 3.35/0.99  
% 3.35/0.99  fof(f32,plain,(
% 3.35/0.99    ( ! [X0,X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k10_lattice3(X0,X1,sK9) != k10_lattice3(X0,sK9,X1) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f31,plain,(
% 3.35/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k10_lattice3(X0,X2,sK8) != k10_lattice3(X0,sK8,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f30,plain,(
% 3.35/0.99    ? [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (k10_lattice3(sK7,X1,X2) != k10_lattice3(sK7,X2,X1) & m1_subset_1(X2,u1_struct_0(sK7))) & m1_subset_1(X1,u1_struct_0(sK7))) & l1_orders_2(sK7) & v1_lattice3(sK7) & v5_orders_2(sK7))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f33,plain,(
% 3.35/0.99    ((k10_lattice3(sK7,sK8,sK9) != k10_lattice3(sK7,sK9,sK8) & m1_subset_1(sK9,u1_struct_0(sK7))) & m1_subset_1(sK8,u1_struct_0(sK7))) & l1_orders_2(sK7) & v1_lattice3(sK7) & v5_orders_2(sK7)),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f13,f32,f31,f30])).
% 3.35/0.99  
% 3.35/0.99  fof(f58,plain,(
% 3.35/0.99    m1_subset_1(sK8,u1_struct_0(sK7))),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f59,plain,(
% 3.35/0.99    m1_subset_1(sK9,u1_struct_0(sK7))),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f14,plain,(
% 3.35/0.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))))),
% 3.35/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.35/0.99  
% 3.35/0.99  fof(f18,plain,(
% 3.35/0.99    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.35/0.99    inference(nnf_transformation,[],[f14])).
% 3.35/0.99  
% 3.35/0.99  fof(f19,plain,(
% 3.35/0.99    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X5] : (! [X6] : (? [X7] : (! [X8] : (r1_orders_2(X0,X7,X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,X7) & r1_orders_2(X0,X5,X7) & m1_subset_1(X7,u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.35/0.99    inference(rectify,[],[f18])).
% 3.35/0.99  
% 3.35/0.99  fof(f23,plain,(
% 3.35/0.99    ! [X6,X5,X0] : (? [X7] : (! [X8] : (r1_orders_2(X0,X7,X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,X7) & r1_orders_2(X0,X5,X7) & m1_subset_1(X7,u1_struct_0(X0))) => (! [X8] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,sK5(X0,X5,X6)) & r1_orders_2(X0,X5,sK5(X0,X5,X6)) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f22,plain,(
% 3.35/0.99    ( ! [X2,X1] : (! [X3,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK4(X0,X3)) & r1_orders_2(X0,X2,sK4(X0,X3)) & r1_orders_2(X0,X1,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f21,plain,(
% 3.35/0.99    ( ! [X1] : (! [X0] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,sK3(X0),X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,sK3(X0),X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f20,plain,(
% 3.35/0.99    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,sK2(X0),X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,sK2(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f24,plain,(
% 3.35/0.99    ! [X0] : ((sP0(X0) | ((! [X3] : ((~r1_orders_2(X0,X3,sK4(X0,X3)) & r1_orders_2(X0,sK3(X0),sK4(X0,X3)) & r1_orders_2(X0,sK2(X0),sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,sK3(X0),X3) | ~r1_orders_2(X0,sK2(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X5] : (! [X6] : ((! [X8] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,sK5(X0,X5,X6)) & r1_orders_2(X0,X5,sK5(X0,X5,X6)) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f23,f22,f21,f20])).
% 3.35/0.99  
% 3.35/0.99  fof(f37,plain,(
% 3.35/0.99    ( ! [X6,X0,X5] : (m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f39,plain,(
% 3.35/0.99    ( ! [X6,X0,X5] : (r1_orders_2(X0,X6,sK5(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f3,axiom,(
% 3.35/0.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f10,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f3])).
% 3.35/0.99  
% 3.35/0.99  fof(f11,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f10])).
% 3.35/0.99  
% 3.35/0.99  fof(f25,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(nnf_transformation,[],[f11])).
% 3.35/0.99  
% 3.35/0.99  fof(f26,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f25])).
% 3.35/0.99  
% 3.35/0.99  fof(f27,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(rectify,[],[f26])).
% 3.35/0.99  
% 3.35/0.99  fof(f28,plain,(
% 3.35/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f29,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).
% 3.35/0.99  
% 3.35/0.99  fof(f52,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f29])).
% 3.35/0.99  
% 3.35/0.99  fof(f1,axiom,(
% 3.35/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f6,plain,(
% 3.35/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f1])).
% 3.35/0.99  
% 3.35/0.99  fof(f7,plain,(
% 3.35/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.35/0.99    inference(flattening,[],[f6])).
% 3.35/0.99  
% 3.35/0.99  fof(f34,plain,(
% 3.35/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f7])).
% 3.35/0.99  
% 3.35/0.99  fof(f55,plain,(
% 3.35/0.99    v5_orders_2(sK7)),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f56,plain,(
% 3.35/0.99    v1_lattice3(sK7)),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f57,plain,(
% 3.35/0.99    l1_orders_2(sK7)),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f53,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f29])).
% 3.35/0.99  
% 3.35/0.99  fof(f40,plain,(
% 3.35/0.99    ( ! [X6,X0,X8,X5] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f54,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f29])).
% 3.35/0.99  
% 3.35/0.99  fof(f2,axiom,(
% 3.35/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f8,plain,(
% 3.35/0.99    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f2])).
% 3.35/0.99  
% 3.35/0.99  fof(f9,plain,(
% 3.35/0.99    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.35/0.99    inference(flattening,[],[f8])).
% 3.35/0.99  
% 3.35/0.99  fof(f15,plain,(
% 3.35/0.99    ! [X0] : ((v1_lattice3(X0) <=> sP0(X0)) | ~sP1(X0))),
% 3.35/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.35/0.99  
% 3.35/0.99  fof(f16,plain,(
% 3.35/0.99    ! [X0] : (sP1(X0) | ~l1_orders_2(X0))),
% 3.35/0.99    inference(definition_folding,[],[f9,f15,f14])).
% 3.35/0.99  
% 3.35/0.99  fof(f47,plain,(
% 3.35/0.99    ( ! [X0] : (sP1(X0) | ~l1_orders_2(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f16])).
% 3.35/0.99  
% 3.35/0.99  fof(f17,plain,(
% 3.35/0.99    ! [X0] : (((v1_lattice3(X0) | ~sP0(X0)) & (sP0(X0) | ~v1_lattice3(X0))) | ~sP1(X0))),
% 3.35/0.99    inference(nnf_transformation,[],[f15])).
% 3.35/0.99  
% 3.35/0.99  fof(f35,plain,(
% 3.35/0.99    ( ! [X0] : (sP0(X0) | ~v1_lattice3(X0) | ~sP1(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f17])).
% 3.35/0.99  
% 3.35/0.99  fof(f51,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f29])).
% 3.35/0.99  
% 3.35/0.99  fof(f38,plain,(
% 3.35/0.99    ( ! [X6,X0,X5] : (r1_orders_2(X0,X5,sK5(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f48,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f29])).
% 3.35/0.99  
% 3.35/0.99  fof(f63,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f48])).
% 3.35/0.99  
% 3.35/0.99  fof(f60,plain,(
% 3.35/0.99    k10_lattice3(sK7,sK8,sK9) != k10_lattice3(sK7,sK9,sK8)),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  cnf(c_23,negated_conjecture,
% 3.35/0.99      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2408,negated_conjecture,
% 3.35/0.99      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2769,plain,
% 3.35/0.99      ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2408]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_22,negated_conjecture,
% 3.35/0.99      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2409,negated_conjecture,
% 3.35/0.99      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2768,plain,
% 3.35/0.99      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_12,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.35/0.99      | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
% 3.35/0.99      | ~ sP0(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2411,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 3.35/0.99      | m1_subset_1(sK5(X0_46,X1_47,X0_47),u1_struct_0(X0_46))
% 3.35/0.99      | ~ sP0(X0_46) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2767,plain,
% 3.35/0.99      ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(X0_46,X0_47,X1_47),u1_struct_0(X0_46)) = iProver_top
% 3.35/0.99      | sP0(X0_46) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_10,plain,
% 3.35/0.99      ( r1_orders_2(X0,X1,sK5(X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ sP0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2413,plain,
% 3.35/0.99      ( r1_orders_2(X0_46,X0_47,sK5(X0_46,X1_47,X0_47))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 3.35/0.99      | ~ sP0(X0_46) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2765,plain,
% 3.35/0.99      ( r1_orders_2(X0_46,X0_47,sK5(X0_46,X1_47,X0_47)) = iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 3.35/0.99      | sP0(X0_46) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2413]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_16,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_0,plain,
% 3.35/0.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_171,plain,
% 3.35/0.99      ( ~ v1_lattice3(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_16,c_0]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_172,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_171]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_26,negated_conjecture,
% 3.35/0.99      ( v5_orders_2(sK7) ),
% 3.35/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_419,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2
% 3.35/0.99      | sK7 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_172,c_26]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_420,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | r1_orders_2(sK7,X0,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | ~ l1_orders_2(sK7)
% 3.35/0.99      | ~ v1_lattice3(sK7)
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_419]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_25,negated_conjecture,
% 3.35/0.99      ( v1_lattice3(sK7) ),
% 3.35/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_24,negated_conjecture,
% 3.35/0.99      ( l1_orders_2(sK7) ),
% 3.35/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_422,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | r1_orders_2(sK7,X0,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_420,c_25,c_24]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_423,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | r1_orders_2(sK7,X0,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_422]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2405,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0_47,X1_47)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2_47,X1_47)
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK6(sK7,X0_47,X2_47,X1_47))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0_47,X2_47) = X1_47 ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_423]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2772,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = X2_47
% 3.35/0.99      | r1_orders_2(sK7,X0_47,X2_47) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,X2_47) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK6(sK7,X0_47,X1_47,X2_47)) = iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2405]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_15,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_178,plain,
% 3.35/0.99      ( ~ v1_lattice3(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_15,c_0]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_179,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_178]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_386,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2
% 3.35/0.99      | sK7 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_179,c_26]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_387,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | r1_orders_2(sK7,X2,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | ~ l1_orders_2(sK7)
% 3.35/0.99      | ~ v1_lattice3(sK7)
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_391,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | r1_orders_2(sK7,X2,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_387,c_25,c_24]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_392,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | r1_orders_2(sK7,X2,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_391]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2406,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0_47,X1_47)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2_47,X1_47)
% 3.35/0.99      | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X2_47,X1_47))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0_47,X2_47) = X1_47 ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_392]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2771,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = X2_47
% 3.35/0.99      | r1_orders_2(sK7,X0_47,X2_47) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,X2_47) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK6(sK7,X0_47,X1_47,X2_47)) = iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2406]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_9,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | r1_orders_2(X0,sK5(X0,X3,X1),X2)
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ sP0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2414,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 3.35/0.99      | ~ r1_orders_2(X0_46,X2_47,X1_47)
% 3.35/0.99      | r1_orders_2(X0_46,sK5(X0_46,X2_47,X0_47),X1_47)
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 3.35/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
% 3.35/0.99      | ~ sP0(X0_46) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2764,plain,
% 3.35/0.99      ( r1_orders_2(X0_46,X0_47,X1_47) != iProver_top
% 3.35/0.99      | r1_orders_2(X0_46,X2_47,X1_47) != iProver_top
% 3.35/0.99      | r1_orders_2(X0_46,sK5(X0_46,X2_47,X0_47),X1_47) = iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(X0_46)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 3.35/0.99      | sP0(X0_46) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_14,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_183,plain,
% 3.35/0.99      ( ~ v1_lattice3(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_14,c_0]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_184,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_183]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_353,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2
% 3.35/0.99      | sK7 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_184,c_26]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_354,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X1,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | ~ l1_orders_2(sK7)
% 3.35/0.99      | ~ v1_lattice3(sK7)
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_358,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X1,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_354,c_25,c_24]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_359,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X1,sK6(sK7,X0,X2,X1))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_358]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2407,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0_47,X1_47)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2_47,X1_47)
% 3.35/0.99      | ~ r1_orders_2(sK7,X1_47,sK6(sK7,X0_47,X2_47,X1_47))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0_47,X2_47) = X1_47 ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_359]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2770,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = X2_47
% 3.35/0.99      | r1_orders_2(sK7,X0_47,X2_47) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,X2_47) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,X2_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2407]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4231,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
% 3.35/0.99      | r1_orders_2(sK7,X3_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X3_47)) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X3_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2764,c_2770]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_28,plain,
% 3.35/0.99      ( v1_lattice3(sK7) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_29,plain,
% 3.35/0.99      ( l1_orders_2(sK7) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_13,plain,
% 3.35/0.99      ( sP1(X0) | ~ l1_orders_2(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_49,plain,
% 3.35/0.99      ( sP1(X0) = iProver_top | l1_orders_2(X0) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_51,plain,
% 3.35/0.99      ( sP1(sK7) = iProver_top | l1_orders_2(sK7) != iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_49]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2,plain,
% 3.35/0.99      ( ~ sP1(X0) | sP0(X0) | ~ v1_lattice3(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_80,plain,
% 3.35/0.99      ( sP1(X0) != iProver_top
% 3.35/0.99      | sP0(X0) = iProver_top
% 3.35/0.99      | v1_lattice3(X0) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_82,plain,
% 3.35/0.99      ( sP1(sK7) != iProver_top
% 3.35/0.99      | sP0(sK7) = iProver_top
% 3.35/0.99      | v1_lattice3(sK7) != iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_80]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_17,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_164,plain,
% 3.35/0.99      ( ~ v1_lattice3(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_17,c_0]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_165,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_164]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_448,plain,
% 3.35/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.35/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | k10_lattice3(X0,X3,X1) = X2
% 3.35/0.99      | sK7 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_165,c_26]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_449,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | m1_subset_1(sK6(sK7,X0,X2,X1),u1_struct_0(sK7))
% 3.35/0.99      | ~ l1_orders_2(sK7)
% 3.35/0.99      | ~ v1_lattice3(sK7)
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_448]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_453,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | m1_subset_1(sK6(sK7,X0,X2,X1),u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_449,c_25,c_24]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_454,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2,X1)
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | m1_subset_1(sK6(sK7,X0,X2,X1),u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0,X2) = X1 ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_453]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2404,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0_47,X1_47)
% 3.35/0.99      | ~ r1_orders_2(sK7,X2_47,X1_47)
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.35/0.99      | m1_subset_1(sK6(sK7,X0_47,X2_47,X1_47),u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0_47,X2_47) = X1_47 ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_454]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3997,plain,
% 3.35/0.99      ( ~ r1_orders_2(sK7,X0_47,sK5(sK7,X1_47,X2_47))
% 3.35/0.99      | ~ r1_orders_2(sK7,X3_47,sK5(sK7,X1_47,X2_47))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X3_47,u1_struct_0(sK7))
% 3.35/0.99      | m1_subset_1(sK6(sK7,X0_47,X3_47,sK5(sK7,X1_47,X2_47)),u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(sK5(sK7,X1_47,X2_47),u1_struct_0(sK7))
% 3.35/0.99      | k10_lattice3(sK7,X0_47,X3_47) = sK5(sK7,X1_47,X2_47) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2404]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4003,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X3_47)) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X3_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),u1_struct_0(sK7)) = iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3997]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4459,plain,
% 3.35/0.99      ( m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
% 3.35/0.99      | r1_orders_2(sK7,X3_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X3_47)) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X3_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_4231,c_28,c_29,c_51,c_82,c_4003]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4460,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
% 3.35/0.99      | r1_orders_2(sK7,X3_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47))) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X3_47)) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X3_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_4459]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4476,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X1_47)
% 3.35/0.99      | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X1_47))) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X1_47)) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X1_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X2_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2771,c_4460]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4556,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK5(sK7,X0_47,X1_47)) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X0_47,X1_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2772,c_4476]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_11,plain,
% 3.35/0.99      ( r1_orders_2(X0,X1,sK5(X0,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ sP0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2412,plain,
% 3.35/0.99      ( r1_orders_2(X0_46,X0_47,sK5(X0_46,X0_47,X1_47))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 3.35/0.99      | ~ sP0(X0_46) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3014,plain,
% 3.35/0.99      ( r1_orders_2(sK7,X0_47,sK5(sK7,X0_47,X1_47))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ sP0(sK7) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2412]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3020,plain,
% 3.35/0.99      ( r1_orders_2(sK7,X0_47,sK5(sK7,X0_47,X1_47)) = iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3014]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4774,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X0_47,X1_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_4556,c_28,c_29,c_51,c_82,c_3020]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4784,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2765,c_4774]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7265,plain,
% 3.35/0.99      ( m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_4784,c_28,c_29,c_51,c_82]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7266,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_7265]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7273,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2767,c_7266]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7374,plain,
% 3.35/0.99      ( m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_7273,c_28,c_29,c_51,c_82]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7375,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_7374]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7381,plain,
% 3.35/0.99      ( k10_lattice3(sK7,sK9,X0_47) = sK5(sK7,sK9,X0_47)
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2768,c_7375]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7434,plain,
% 3.35/0.99      ( k10_lattice3(sK7,sK9,sK8) = sK5(sK7,sK9,sK8) ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2769,c_7381]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_20,plain,
% 3.35/0.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | v2_struct_0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_145,plain,
% 3.35/0.99      ( ~ v1_lattice3(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_20,c_0]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_146,plain,
% 3.35/0.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.35/0.99      | ~ v5_orders_2(X0)
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0) ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_145]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_538,plain,
% 3.35/0.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.35/0.99      | ~ l1_orders_2(X0)
% 3.35/0.99      | ~ v1_lattice3(X0)
% 3.35/0.99      | sK7 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_146,c_26]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_539,plain,
% 3.35/0.99      ( r1_orders_2(sK7,X0,k10_lattice3(sK7,X0,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(k10_lattice3(sK7,X0,X1),u1_struct_0(sK7))
% 3.35/0.99      | ~ l1_orders_2(sK7)
% 3.35/0.99      | ~ v1_lattice3(sK7) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_538]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_541,plain,
% 3.35/0.99      ( r1_orders_2(sK7,X0,k10_lattice3(sK7,X0,X1))
% 3.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(k10_lattice3(sK7,X0,X1),u1_struct_0(sK7)) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_539,c_25,c_24]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2401,plain,
% 3.35/0.99      ( r1_orders_2(sK7,X0_47,k10_lattice3(sK7,X0_47,X1_47))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(k10_lattice3(sK7,X0_47,X1_47),u1_struct_0(sK7)) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_541]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2776,plain,
% 3.35/0.99      ( r1_orders_2(sK7,X0_47,k10_lattice3(sK7,X0_47,X1_47)) = iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(k10_lattice3(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2401]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7624,plain,
% 3.35/0.99      ( r1_orders_2(sK7,sK9,k10_lattice3(sK7,sK9,sK8)) = iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_7434,c_2776]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7655,plain,
% 3.35/0.99      ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,sK8)) = iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(light_normalisation,[status(thm)],[c_7624,c_7434]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_30,plain,
% 3.35/0.99      ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_31,plain,
% 3.35/0.99      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3376,plain,
% 3.35/0.99      ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,X0_47))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.35/0.99      | ~ sP0(sK7) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_3014]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3377,plain,
% 3.35/0.99      ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,X0_47)) = iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3376]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3379,plain,
% 3.35/0.99      ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,sK8)) = iProver_top
% 3.35/0.99      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_3377]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_8122,plain,
% 3.35/0.99      ( r1_orders_2(sK7,sK9,sK5(sK7,sK9,sK8)) = iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_7655,c_28,c_29,c_30,c_31,c_51,c_82,c_3379]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4477,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X0_47)
% 3.35/0.99      | r1_orders_2(sK7,X2_47,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X0_47))) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK5(sK7,X2_47,X0_47)) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X2_47,X0_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X2_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2772,c_4460]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4961,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X1_47,X0_47)
% 3.35/0.99      | r1_orders_2(sK7,X0_47,sK5(sK7,X1_47,X0_47)) != iProver_top
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X1_47,X0_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X1_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2771,c_4477]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3040,plain,
% 3.35/0.99      ( r1_orders_2(sK7,X0_47,sK5(sK7,X1_47,X0_47))
% 3.35/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | ~ sP0(sK7) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2413]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3046,plain,
% 3.35/0.99      ( r1_orders_2(sK7,X0_47,sK5(sK7,X1_47,X0_47)) = iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3040]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5017,plain,
% 3.35/0.99      ( k10_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X1_47,X0_47)
% 3.35/0.99      | r1_orders_2(sK7,X1_47,sK5(sK7,X1_47,X0_47)) != iProver_top
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,X1_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_4961,c_28,c_29,c_51,c_82,c_3046]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_8130,plain,
% 3.35/0.99      ( k10_lattice3(sK7,sK8,sK9) = sK5(sK7,sK9,sK8)
% 3.35/0.99      | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_8122,c_5017]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7382,plain,
% 3.35/0.99      ( k10_lattice3(sK7,sK8,X0_47) = sK5(sK7,sK8,X0_47)
% 3.35/0.99      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2769,c_7375]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7805,plain,
% 3.35/0.99      ( k10_lattice3(sK7,sK8,sK9) = sK5(sK7,sK8,sK9) ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2768,c_7382]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_8135,plain,
% 3.35/0.99      ( sK5(sK7,sK8,sK9) = sK5(sK7,sK9,sK8)
% 3.35/0.99      | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
% 3.35/0.99      inference(light_normalisation,[status(thm)],[c_8130,c_7805]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_21,negated_conjecture,
% 3.35/0.99      ( k10_lattice3(sK7,sK8,sK9) != k10_lattice3(sK7,sK9,sK8) ),
% 3.35/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2410,negated_conjecture,
% 3.35/0.99      ( k10_lattice3(sK7,sK8,sK9) != k10_lattice3(sK7,sK9,sK8) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7623,plain,
% 3.35/0.99      ( k10_lattice3(sK7,sK8,sK9) != sK5(sK7,sK9,sK8) ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_7434,c_2410]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7841,plain,
% 3.35/0.99      ( sK5(sK7,sK8,sK9) != sK5(sK7,sK9,sK8) ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_7805,c_7623]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5126,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.35/0.99      | m1_subset_1(sK5(sK7,sK9,X0_47),u1_struct_0(sK7))
% 3.35/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.35/0.99      | ~ sP0(sK7) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2411]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5127,plain,
% 3.35/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK5(sK7,sK9,X0_47),u1_struct_0(sK7)) = iProver_top
% 3.35/0.99      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_5126]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5129,plain,
% 3.35/0.99      ( m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) = iProver_top
% 3.35/0.99      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 3.35/0.99      | sP0(sK7) != iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_5127]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(contradiction,plain,
% 3.35/0.99      ( $false ),
% 3.35/0.99      inference(minisat,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_8135,c_7841,c_5129,c_82,c_51,c_31,c_30,c_29,c_28]) ).
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  ------                               Statistics
% 3.35/0.99  
% 3.35/0.99  ------ General
% 3.35/0.99  
% 3.35/0.99  abstr_ref_over_cycles:                  0
% 3.35/0.99  abstr_ref_under_cycles:                 0
% 3.35/0.99  gc_basic_clause_elim:                   0
% 3.35/0.99  forced_gc_time:                         0
% 3.35/0.99  parsing_time:                           0.019
% 3.35/0.99  unif_index_cands_time:                  0.
% 3.35/0.99  unif_index_add_time:                    0.
% 3.35/0.99  orderings_time:                         0.
% 3.35/0.99  out_proof_time:                         0.013
% 3.35/0.99  total_time:                             0.367
% 3.35/0.99  num_of_symbols:                         49
% 3.35/0.99  num_of_terms:                           8040
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing
% 3.35/0.99  
% 3.35/0.99  num_of_splits:                          0
% 3.35/0.99  num_of_split_atoms:                     0
% 3.35/0.99  num_of_reused_defs:                     0
% 3.35/0.99  num_eq_ax_congr_red:                    41
% 3.35/0.99  num_of_sem_filtered_clauses:            2
% 3.35/0.99  num_of_subtypes:                        3
% 3.35/0.99  monotx_restored_types:                  0
% 3.35/0.99  sat_num_of_epr_types:                   0
% 3.35/0.99  sat_num_of_non_cyclic_types:            0
% 3.35/0.99  sat_guarded_non_collapsed_types:        1
% 3.35/0.99  num_pure_diseq_elim:                    0
% 3.35/0.99  simp_replaced_by:                       0
% 3.35/0.99  res_preprocessed:                       101
% 3.35/0.99  prep_upred:                             0
% 3.35/0.99  prep_unflattend:                        29
% 3.35/0.99  smt_new_axioms:                         0
% 3.35/0.99  pred_elim_cands:                        3
% 3.35/0.99  pred_elim:                              4
% 3.35/0.99  pred_elim_cl:                           5
% 3.35/0.99  pred_elim_cycles:                       6
% 3.35/0.99  merged_defs:                            0
% 3.35/0.99  merged_defs_ncl:                        0
% 3.35/0.99  bin_hyper_res:                          0
% 3.35/0.99  prep_cycles:                            4
% 3.35/0.99  pred_elim_time:                         0.061
% 3.35/0.99  splitting_time:                         0.
% 3.35/0.99  sem_filter_time:                        0.
% 3.35/0.99  monotx_time:                            0.
% 3.35/0.99  subtype_inf_time:                       0.
% 3.35/0.99  
% 3.35/0.99  ------ Problem properties
% 3.35/0.99  
% 3.35/0.99  clauses:                                21
% 3.35/0.99  conjectures:                            3
% 3.35/0.99  epr:                                    1
% 3.35/0.99  horn:                                   13
% 3.35/0.99  ground:                                 4
% 3.35/0.99  unary:                                  4
% 3.35/0.99  binary:                                 2
% 3.35/0.99  lits:                                   90
% 3.35/0.99  lits_eq:                                5
% 3.35/0.99  fd_pure:                                0
% 3.35/0.99  fd_pseudo:                              0
% 3.35/0.99  fd_cond:                                0
% 3.35/0.99  fd_pseudo_cond:                         4
% 3.35/0.99  ac_symbols:                             0
% 3.35/0.99  
% 3.35/0.99  ------ Propositional Solver
% 3.35/0.99  
% 3.35/0.99  prop_solver_calls:                      29
% 3.35/0.99  prop_fast_solver_calls:                 1754
% 3.35/0.99  smt_solver_calls:                       0
% 3.35/0.99  smt_fast_solver_calls:                  0
% 3.35/0.99  prop_num_of_clauses:                    1752
% 3.35/0.99  prop_preprocess_simplified:             5637
% 3.35/0.99  prop_fo_subsumed:                       53
% 3.35/0.99  prop_solver_time:                       0.
% 3.35/0.99  smt_solver_time:                        0.
% 3.35/0.99  smt_fast_solver_time:                   0.
% 3.35/0.99  prop_fast_solver_time:                  0.
% 3.35/0.99  prop_unsat_core_time:                   0.
% 3.35/0.99  
% 3.35/0.99  ------ QBF
% 3.35/0.99  
% 3.35/0.99  qbf_q_res:                              0
% 3.35/0.99  qbf_num_tautologies:                    0
% 3.35/0.99  qbf_prep_cycles:                        0
% 3.35/0.99  
% 3.35/0.99  ------ BMC1
% 3.35/0.99  
% 3.35/0.99  bmc1_current_bound:                     -1
% 3.35/0.99  bmc1_last_solved_bound:                 -1
% 3.35/0.99  bmc1_unsat_core_size:                   -1
% 3.35/0.99  bmc1_unsat_core_parents_size:           -1
% 3.35/0.99  bmc1_merge_next_fun:                    0
% 3.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation
% 3.35/0.99  
% 3.35/0.99  inst_num_of_clauses:                    462
% 3.35/0.99  inst_num_in_passive:                    211
% 3.35/0.99  inst_num_in_active:                     245
% 3.35/0.99  inst_num_in_unprocessed:                6
% 3.35/0.99  inst_num_of_loops:                      300
% 3.35/0.99  inst_num_of_learning_restarts:          0
% 3.35/0.99  inst_num_moves_active_passive:          51
% 3.35/0.99  inst_lit_activity:                      0
% 3.35/0.99  inst_lit_activity_moves:                0
% 3.35/0.99  inst_num_tautologies:                   0
% 3.35/0.99  inst_num_prop_implied:                  0
% 3.35/0.99  inst_num_existing_simplified:           0
% 3.35/0.99  inst_num_eq_res_simplified:             0
% 3.35/0.99  inst_num_child_elim:                    0
% 3.35/0.99  inst_num_of_dismatching_blockings:      641
% 3.35/0.99  inst_num_of_non_proper_insts:           841
% 3.35/0.99  inst_num_of_duplicates:                 0
% 3.35/0.99  inst_inst_num_from_inst_to_res:         0
% 3.35/0.99  inst_dismatching_checking_time:         0.
% 3.35/0.99  
% 3.35/0.99  ------ Resolution
% 3.35/0.99  
% 3.35/0.99  res_num_of_clauses:                     0
% 3.35/0.99  res_num_in_passive:                     0
% 3.35/0.99  res_num_in_active:                      0
% 3.35/0.99  res_num_of_loops:                       105
% 3.35/0.99  res_forward_subset_subsumed:            29
% 3.35/0.99  res_backward_subset_subsumed:           0
% 3.35/0.99  res_forward_subsumed:                   0
% 3.35/0.99  res_backward_subsumed:                  0
% 3.35/0.99  res_forward_subsumption_resolution:     0
% 3.35/0.99  res_backward_subsumption_resolution:    0
% 3.35/0.99  res_clause_to_clause_subsumption:       1905
% 3.35/0.99  res_orphan_elimination:                 0
% 3.35/0.99  res_tautology_del:                      23
% 3.35/0.99  res_num_eq_res_simplified:              0
% 3.35/0.99  res_num_sel_changes:                    0
% 3.35/0.99  res_moves_from_active_to_pass:          0
% 3.35/0.99  
% 3.35/0.99  ------ Superposition
% 3.35/0.99  
% 3.35/0.99  sup_time_total:                         0.
% 3.35/0.99  sup_time_generating:                    0.
% 3.35/0.99  sup_time_sim_full:                      0.
% 3.35/0.99  sup_time_sim_immed:                     0.
% 3.35/0.99  
% 3.35/0.99  sup_num_of_clauses:                     126
% 3.35/0.99  sup_num_in_active:                      54
% 3.35/0.99  sup_num_in_passive:                     72
% 3.35/0.99  sup_num_of_loops:                       58
% 3.35/0.99  sup_fw_superposition:                   83
% 3.35/0.99  sup_bw_superposition:                   70
% 3.35/0.99  sup_immediate_simplified:               44
% 3.35/0.99  sup_given_eliminated:                   0
% 3.35/0.99  comparisons_done:                       0
% 3.35/0.99  comparisons_avoided:                    12
% 3.35/0.99  
% 3.35/0.99  ------ Simplifications
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  sim_fw_subset_subsumed:                 29
% 3.35/0.99  sim_bw_subset_subsumed:                 3
% 3.35/0.99  sim_fw_subsumed:                        2
% 3.35/0.99  sim_bw_subsumed:                        2
% 3.35/0.99  sim_fw_subsumption_res:                 0
% 3.35/0.99  sim_bw_subsumption_res:                 0
% 3.35/0.99  sim_tautology_del:                      1
% 3.35/0.99  sim_eq_tautology_del:                   0
% 3.35/0.99  sim_eq_res_simp:                        0
% 3.35/0.99  sim_fw_demodulated:                     0
% 3.35/0.99  sim_bw_demodulated:                     2
% 3.35/0.99  sim_light_normalised:                   11
% 3.35/0.99  sim_joinable_taut:                      0
% 3.35/0.99  sim_joinable_simp:                      0
% 3.35/0.99  sim_ac_normalised:                      0
% 3.35/0.99  sim_smt_subsumption:                    0
% 3.35/0.99  
%------------------------------------------------------------------------------
