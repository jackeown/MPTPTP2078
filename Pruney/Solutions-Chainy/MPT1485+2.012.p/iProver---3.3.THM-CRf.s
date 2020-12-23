%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:05 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  230 ( 714 expanded)
%              Number of clauses        :  156 ( 204 expanded)
%              Number of leaves         :   24 ( 219 expanded)
%              Depth                    :   19
%              Number of atoms          : 1497 (5378 expanded)
%              Number of equality atoms :  264 ( 721 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
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

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f31,f35,f34,f33,f32])).

fof(f58,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK5(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK5(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,conjecture,(
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
             => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
               => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK10)) != X1
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k12_lattice3(X0,sK9,k13_lattice3(X0,sK9,X2)) != sK9
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(sK8,X1,k13_lattice3(sK8,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK8)) )
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & l1_orders_2(sK8)
      & v2_lattice3(sK8)
      & v1_lattice3(sK8)
      & v5_orders_2(sK8)
      & v3_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9
    & m1_subset_1(sK10,u1_struct_0(sK8))
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l1_orders_2(sK8)
    & v2_lattice3(sK8)
    & v1_lattice3(sK8)
    & v5_orders_2(sK8)
    & v3_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f25,f49,f48,f47])).

fof(f83,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f41])).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f56,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK5(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
    inference(cnf_transformation,[],[f50])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f15,f27,f26])).

fof(f65,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK5(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2943,plain,
    ( ~ r1_orders_2(X0_52,X0_53,X1_53)
    | ~ r1_orders_2(X0_52,X2_53,X1_53)
    | r1_orders_2(X0_52,sK5(X0_52,X2_53,X0_53),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_15051,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),X1_53)
    | ~ r1_orders_2(sK8,sK10,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_22602,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X1_53)))
    | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X1_53)))
    | ~ r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X1_53)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X1_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_15051])).

cnf(c_22604,plain,
    ( r1_orders_2(sK8,sK5(sK8,sK10,sK9),sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
    | ~ r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
    | ~ r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
    | ~ m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_22602])).

cnf(c_2953,plain,
    ( ~ r1_orders_2(X0_52,X0_53,X1_53)
    | r1_orders_2(X0_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_8182,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | k10_lattice3(sK8,sK9,sK10) != X1_53
    | sK9 != X0_53 ),
    inference(instantiation,[status(thm)],[c_2953])).

cnf(c_11782,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X1_53))
    | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X1_53)
    | sK9 != X0_53 ),
    inference(instantiation,[status(thm)],[c_8182])).

cnf(c_11785,plain,
    ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53)
    | sK9 != X1_53
    | r1_orders_2(sK8,X1_53,sK5(sK8,sK10,X0_53)) != iProver_top
    | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11782])).

cnf(c_11787,plain,
    ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,sK9)
    | sK9 != sK9
    | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11785])).

cnf(c_2954,plain,
    ( ~ m1_subset_1(X0_53,X0_54)
    | m1_subset_1(X1_53,X0_54)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_3875,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(X1_53,u1_struct_0(sK8))
    | X1_53 != X0_53 ),
    inference(instantiation,[status(thm)],[c_2954])).

cnf(c_4376,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) != X0_53 ),
    inference(instantiation,[status(thm)],[c_3875])).

cnf(c_11774,plain,
    ( m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_4376])).

cnf(c_11775,plain,
    ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53)
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11774])).

cnf(c_11777,plain,
    ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,sK9)
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11775])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2940,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | m1_subset_1(sK5(X0_52,X1_53,X0_53),u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_9365,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_2940])).

cnf(c_9366,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9365])).

cnf(c_9368,plain,
    ( m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9366])).

cnf(c_9367,plain,
    ( m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_9365])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2942,plain,
    ( r1_orders_2(X0_52,X0_53,sK5(X0_52,X1_53,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_7021,plain,
    ( r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_7024,plain,
    ( r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7021])).

cnf(c_15,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_258,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_1])).

cnf(c_259,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_37,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_782,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_259,c_37])).

cnf(c_783,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_36,negated_conjecture,
    ( v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_787,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_783,c_36,c_34])).

cnf(c_788,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_787])).

cnf(c_2927,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | ~ r1_orders_2(sK8,X1_53,sK6(sK8,X0_53,X2_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_53,X2_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_788])).

cnf(c_4921,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK10,X0_53)
    | ~ r1_orders_2(sK8,sK9,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2927])).

cnf(c_6867,plain,
    ( ~ r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_4921])).

cnf(c_6880,plain,
    ( ~ r1_orders_2(sK8,sK5(sK8,sK10,sK9),sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
    | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_6867])).

cnf(c_18,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X3,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_239,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK6(X0,X1,X3,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_1])).

cnf(c_240,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X3,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_877,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X3,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_240,c_37])).

cnf(c_878,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X2,X1),u1_struct_0(sK8))
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_882,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X2,X1),u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_878,c_36,c_34])).

cnf(c_883,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X2,X1),u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_882])).

cnf(c_2924,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0_53,X2_53,X1_53),u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_53,X2_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_883])).

cnf(c_4924,plain,
    ( ~ r1_orders_2(sK8,sK10,X0_53)
    | ~ r1_orders_2(sK8,sK9,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,sK9,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2924])).

cnf(c_6868,plain,
    ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
    | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_4924])).

cnf(c_6876,plain,
    ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
    | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_6868])).

cnf(c_17,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_246,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK6(X0,X1,X3,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_1])).

cnf(c_247,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_848,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_247,c_37])).

cnf(c_849,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_851,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_849,c_36,c_34])).

cnf(c_852,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_851])).

cnf(c_2925,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | r1_orders_2(sK8,X0_53,sK6(sK8,X0_53,X2_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_53,X2_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_852])).

cnf(c_4923,plain,
    ( ~ r1_orders_2(sK8,sK10,X0_53)
    | ~ r1_orders_2(sK8,sK9,X0_53)
    | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2925])).

cnf(c_6869,plain,
    ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_4923])).

cnf(c_6872,plain,
    ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
    | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
    | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_6869])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,negated_conjecture,
    ( v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_612,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_613,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_122,plain,
    ( ~ v1_lattice3(sK8)
    | ~ v2_struct_0(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,X0,X1)
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_37,c_36,c_34,c_122])).

cnf(c_618,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_617])).

cnf(c_2931,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_618])).

cnf(c_6836,plain,
    ( r1_orders_2(sK8,sK7(sK8,X0_53,k10_lattice3(sK8,sK9,sK10),sK9),X0_53)
    | ~ r1_orders_2(sK8,sK9,X0_53)
    | ~ r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = sK9 ),
    inference(instantiation,[status(thm)],[c_2931])).

cnf(c_6852,plain,
    ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = sK9
    | r1_orders_2(sK8,sK7(sK8,X0_53,k10_lattice3(sK8,sK9,sK10),sK9),X0_53) = iProver_top
    | r1_orders_2(sK8,sK9,X0_53) != iProver_top
    | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6836])).

cnf(c_6854,plain,
    ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = sK9
    | r1_orders_2(sK8,sK7(sK8,sK9,k10_lattice3(sK8,sK9,sK10),sK9),sK9) = iProver_top
    | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != iProver_top
    | r1_orders_2(sK8,sK9,sK9) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6852])).

cnf(c_22,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_674,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_675,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_679,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,X0,X1)
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_37,c_36,c_34,c_122])).

cnf(c_680,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_2929,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | ~ r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_680])).

cnf(c_6838,plain,
    ( ~ r1_orders_2(sK8,sK7(sK8,X0_53,k10_lattice3(sK8,sK9,sK10),sK9),sK9)
    | ~ r1_orders_2(sK8,sK9,X0_53)
    | ~ r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = sK9 ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_6844,plain,
    ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = sK9
    | r1_orders_2(sK8,sK7(sK8,X0_53,k10_lattice3(sK8,sK9,sK10),sK9),sK9) != iProver_top
    | r1_orders_2(sK8,sK9,X0_53) != iProver_top
    | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6838])).

cnf(c_6846,plain,
    ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = sK9
    | r1_orders_2(sK8,sK7(sK8,sK9,k10_lattice3(sK8,sK9,sK10),sK9),sK9) != iProver_top
    | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != iProver_top
    | r1_orders_2(sK8,sK9,sK9) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6844])).

cnf(c_2952,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_4269,plain,
    ( k11_lattice3(sK8,X0_53,X1_53) != X2_53
    | sK9 != X2_53
    | sK9 = k11_lattice3(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_2952])).

cnf(c_6183,plain,
    ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) != X1_53
    | sK9 != X1_53
    | sK9 = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_6184,plain,
    ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != sK9
    | sK9 = k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_6183])).

cnf(c_12,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2941,plain,
    ( r1_orders_2(X0_52,X0_53,sK5(X0_52,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_5459,plain,
    ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_2941])).

cnf(c_5465,plain,
    ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_5459])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_253,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_1])).

cnf(c_254,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2 ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_815,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_37])).

cnf(c_816,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_815])).

cnf(c_820,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_816,c_36,c_34])).

cnf(c_821,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK6(sK8,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_820])).

cnf(c_2926,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | r1_orders_2(sK8,X2_53,sK6(sK8,X0_53,X2_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_53,X2_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_821])).

cnf(c_4922,plain,
    ( ~ r1_orders_2(sK8,sK10,X0_53)
    | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK9,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2926])).

cnf(c_5458,plain,
    ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_4922])).

cnf(c_5461,plain,
    ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
    | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_5458])).

cnf(c_3951,plain,
    ( k12_lattice3(sK8,X0_53,X1_53) != X2_53
    | sK9 != X2_53
    | sK9 = k12_lattice3(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_2952])).

cnf(c_4154,plain,
    ( k12_lattice3(sK8,X0_53,X1_53) != k11_lattice3(sK8,X0_53,X1_53)
    | sK9 = k12_lattice3(sK8,X0_53,X1_53)
    | sK9 != k11_lattice3(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_3951])).

cnf(c_4997,plain,
    ( k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) != k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | sK9 = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | sK9 != k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_4154])).

cnf(c_4998,plain,
    ( k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | sK9 = k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | sK9 != k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_4997])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_35])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k12_lattice3(sK8,X0,X1) = k11_lattice3(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k12_lattice3(sK8,X0,X1) = k11_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_37,c_34])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k12_lattice3(sK8,X1,X0) = k11_lattice3(sK8,X1,X0) ),
    inference(renaming,[status(thm)],[c_712])).

cnf(c_2928,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | k12_lattice3(sK8,X1_53,X0_53) = k11_lattice3(sK8,X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_713])).

cnf(c_4943,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_4948,plain,
    ( k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4943])).

cnf(c_4950,plain,
    ( k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4948])).

cnf(c_3857,plain,
    ( X0_53 != X1_53
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != X1_53
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2952])).

cnf(c_4002,plain,
    ( X0_53 != k12_lattice3(sK8,X1_53,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = X0_53
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,X1_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_3857])).

cnf(c_4003,plain,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = sK9
    | sK9 != k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_4002])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_987,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_37])).

cnf(c_988,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_992,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_36,c_34])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k13_lattice3(sK8,X1,X0) = k10_lattice3(sK8,X1,X0) ),
    inference(renaming,[status(thm)],[c_992])).

cnf(c_2920,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | k13_lattice3(sK8,X1_53,X0_53) = k10_lattice3(sK8,X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_993])).

cnf(c_3954,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k13_lattice3(sK8,sK9,sK10) = k10_lattice3(sK8,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_2920])).

cnf(c_2955,plain,
    ( X0_53 != X1_53
    | X2_53 != X3_53
    | k12_lattice3(X0_52,X0_53,X2_53) = k12_lattice3(X0_52,X1_53,X3_53) ),
    theory(equality)).

cnf(c_3859,plain,
    ( k13_lattice3(sK8,sK9,sK10) != X0_53
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X1_53,X0_53)
    | sK9 != X1_53 ),
    inference(instantiation,[status(thm)],[c_2955])).

cnf(c_3953,plain,
    ( k13_lattice3(sK8,sK9,sK10) != k10_lattice3(sK8,sK9,sK10)
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | sK9 != X0_53 ),
    inference(instantiation,[status(thm)],[c_3859])).

cnf(c_3955,plain,
    ( k13_lattice3(sK8,sK9,sK10) != k10_lattice3(sK8,sK9,sK10)
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_3953])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_38,negated_conjecture,
    ( v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_447,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_38])).

cnf(c_448,plain,
    ( r1_orders_2(sK8,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_452,plain,
    ( r1_orders_2(sK8,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_36,c_34,c_122])).

cnf(c_2936,plain,
    ( r1_orders_2(sK8,X0_53,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_2981,plain,
    ( r1_orders_2(sK8,X0_53,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2936])).

cnf(c_2983,plain,
    ( r1_orders_2(sK8,sK9,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2981])).

cnf(c_31,negated_conjecture,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2939,negated_conjecture,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2951,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2962,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_2951])).

cnf(c_3,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_117,plain,
    ( sP1(X0) != iProver_top
    | sP0(X0) = iProver_top
    | v1_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_119,plain,
    ( sP1(sK8) != iProver_top
    | sP0(sK8) = iProver_top
    | v1_lattice3(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_118,plain,
    ( ~ sP1(sK8)
    | sP0(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( sP1(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_86,plain,
    ( sP1(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_88,plain,
    ( sP1(sK8) = iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_87,plain,
    ( sP1(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_45,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_44,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_41,plain,
    ( v1_lattice3(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22604,c_11787,c_11777,c_9368,c_9367,c_7024,c_7021,c_6880,c_6876,c_6872,c_6854,c_6846,c_6184,c_5465,c_5461,c_4998,c_4950,c_4003,c_3954,c_3955,c_2983,c_2939,c_2962,c_119,c_118,c_88,c_87,c_45,c_32,c_44,c_33,c_43,c_34,c_41,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:56:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.73/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.49  
% 7.73/1.49  ------  iProver source info
% 7.73/1.49  
% 7.73/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.49  git: non_committed_changes: false
% 7.73/1.49  git: last_make_outside_of_git: false
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    --mode clausify
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.49  --prep_def_merge_mbd                    true
% 7.73/1.49  --prep_def_merge_tr_red                 false
% 7.73/1.49  --prep_def_merge_tr_cl                  false
% 7.73/1.49  --smt_preprocessing                     true
% 7.73/1.49  --smt_ac_axioms                         fast
% 7.73/1.49  --preprocessed_out                      false
% 7.73/1.49  --preprocessed_stats                    false
% 7.73/1.49  
% 7.73/1.49  ------ Abstraction refinement Options
% 7.73/1.49  
% 7.73/1.49  --abstr_ref                             []
% 7.73/1.49  --abstr_ref_prep                        false
% 7.73/1.49  --abstr_ref_until_sat                   false
% 7.73/1.49  --abstr_ref_sig_restrict                funpre
% 7.73/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.49  --abstr_ref_under                       []
% 7.73/1.49  
% 7.73/1.49  ------ SAT Options
% 7.73/1.49  
% 7.73/1.49  --sat_mode                              false
% 7.73/1.49  --sat_fm_restart_options                ""
% 7.73/1.49  --sat_gr_def                            false
% 7.73/1.49  --sat_epr_types                         true
% 7.73/1.49  --sat_non_cyclic_types                  false
% 7.73/1.49  --sat_finite_models                     false
% 7.73/1.49  --sat_fm_lemmas                         false
% 7.73/1.49  --sat_fm_prep                           false
% 7.73/1.49  --sat_fm_uc_incr                        true
% 7.73/1.49  --sat_out_model                         small
% 7.73/1.49  --sat_out_clauses                       false
% 7.73/1.49  
% 7.73/1.49  ------ QBF Options
% 7.73/1.49  
% 7.73/1.49  --qbf_mode                              false
% 7.73/1.49  --qbf_elim_univ                         false
% 7.73/1.49  --qbf_dom_inst                          none
% 7.73/1.49  --qbf_dom_pre_inst                      false
% 7.73/1.49  --qbf_sk_in                             false
% 7.73/1.49  --qbf_pred_elim                         true
% 7.73/1.49  --qbf_split                             512
% 7.73/1.49  
% 7.73/1.49  ------ BMC1 Options
% 7.73/1.49  
% 7.73/1.49  --bmc1_incremental                      false
% 7.73/1.49  --bmc1_axioms                           reachable_all
% 7.73/1.49  --bmc1_min_bound                        0
% 7.73/1.49  --bmc1_max_bound                        -1
% 7.73/1.49  --bmc1_max_bound_default                -1
% 7.73/1.49  --bmc1_symbol_reachability              true
% 7.73/1.49  --bmc1_property_lemmas                  false
% 7.73/1.49  --bmc1_k_induction                      false
% 7.73/1.49  --bmc1_non_equiv_states                 false
% 7.73/1.49  --bmc1_deadlock                         false
% 7.73/1.49  --bmc1_ucm                              false
% 7.73/1.49  --bmc1_add_unsat_core                   none
% 7.73/1.49  --bmc1_unsat_core_children              false
% 7.73/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.49  --bmc1_out_stat                         full
% 7.73/1.49  --bmc1_ground_init                      false
% 7.73/1.49  --bmc1_pre_inst_next_state              false
% 7.73/1.49  --bmc1_pre_inst_state                   false
% 7.73/1.49  --bmc1_pre_inst_reach_state             false
% 7.73/1.49  --bmc1_out_unsat_core                   false
% 7.73/1.49  --bmc1_aig_witness_out                  false
% 7.73/1.49  --bmc1_verbose                          false
% 7.73/1.49  --bmc1_dump_clauses_tptp                false
% 7.73/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.49  --bmc1_dump_file                        -
% 7.73/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.49  --bmc1_ucm_extend_mode                  1
% 7.73/1.49  --bmc1_ucm_init_mode                    2
% 7.73/1.49  --bmc1_ucm_cone_mode                    none
% 7.73/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.49  --bmc1_ucm_relax_model                  4
% 7.73/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.49  --bmc1_ucm_layered_model                none
% 7.73/1.49  --bmc1_ucm_max_lemma_size               10
% 7.73/1.49  
% 7.73/1.49  ------ AIG Options
% 7.73/1.49  
% 7.73/1.49  --aig_mode                              false
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation Options
% 7.73/1.49  
% 7.73/1.49  --instantiation_flag                    true
% 7.73/1.49  --inst_sos_flag                         false
% 7.73/1.49  --inst_sos_phase                        true
% 7.73/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel_side                     num_symb
% 7.73/1.49  --inst_solver_per_active                1400
% 7.73/1.49  --inst_solver_calls_frac                1.
% 7.73/1.49  --inst_passive_queue_type               priority_queues
% 7.73/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.49  --inst_passive_queues_freq              [25;2]
% 7.73/1.49  --inst_dismatching                      true
% 7.73/1.49  --inst_eager_unprocessed_to_passive     true
% 7.73/1.49  --inst_prop_sim_given                   true
% 7.73/1.49  --inst_prop_sim_new                     false
% 7.73/1.49  --inst_subs_new                         false
% 7.73/1.49  --inst_eq_res_simp                      false
% 7.73/1.49  --inst_subs_given                       false
% 7.73/1.49  --inst_orphan_elimination               true
% 7.73/1.49  --inst_learning_loop_flag               true
% 7.73/1.49  --inst_learning_start                   3000
% 7.73/1.49  --inst_learning_factor                  2
% 7.73/1.49  --inst_start_prop_sim_after_learn       3
% 7.73/1.49  --inst_sel_renew                        solver
% 7.73/1.49  --inst_lit_activity_flag                true
% 7.73/1.49  --inst_restr_to_given                   false
% 7.73/1.49  --inst_activity_threshold               500
% 7.73/1.49  --inst_out_proof                        true
% 7.73/1.49  
% 7.73/1.49  ------ Resolution Options
% 7.73/1.49  
% 7.73/1.49  --resolution_flag                       true
% 7.73/1.49  --res_lit_sel                           adaptive
% 7.73/1.49  --res_lit_sel_side                      none
% 7.73/1.49  --res_ordering                          kbo
% 7.73/1.49  --res_to_prop_solver                    active
% 7.73/1.49  --res_prop_simpl_new                    false
% 7.73/1.49  --res_prop_simpl_given                  true
% 7.73/1.49  --res_passive_queue_type                priority_queues
% 7.73/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.49  --res_passive_queues_freq               [15;5]
% 7.73/1.49  --res_forward_subs                      full
% 7.73/1.49  --res_backward_subs                     full
% 7.73/1.49  --res_forward_subs_resolution           true
% 7.73/1.49  --res_backward_subs_resolution          true
% 7.73/1.49  --res_orphan_elimination                true
% 7.73/1.49  --res_time_limit                        2.
% 7.73/1.49  --res_out_proof                         true
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Options
% 7.73/1.49  
% 7.73/1.49  --superposition_flag                    true
% 7.73/1.49  --sup_passive_queue_type                priority_queues
% 7.73/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.49  --demod_completeness_check              fast
% 7.73/1.49  --demod_use_ground                      true
% 7.73/1.49  --sup_to_prop_solver                    passive
% 7.73/1.49  --sup_prop_simpl_new                    true
% 7.73/1.49  --sup_prop_simpl_given                  true
% 7.73/1.49  --sup_fun_splitting                     false
% 7.73/1.49  --sup_smt_interval                      50000
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Simplification Setup
% 7.73/1.49  
% 7.73/1.49  --sup_indices_passive                   []
% 7.73/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_full_bw                           [BwDemod]
% 7.73/1.49  --sup_immed_triv                        [TrivRules]
% 7.73/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_immed_bw_main                     []
% 7.73/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.49  
% 7.73/1.49  ------ Combination Options
% 7.73/1.49  
% 7.73/1.49  --comb_res_mult                         3
% 7.73/1.49  --comb_sup_mult                         2
% 7.73/1.49  --comb_inst_mult                        10
% 7.73/1.49  
% 7.73/1.49  ------ Debug Options
% 7.73/1.49  
% 7.73/1.49  --dbg_backtrace                         false
% 7.73/1.49  --dbg_dump_prop_clauses                 false
% 7.73/1.49  --dbg_dump_prop_clauses_file            -
% 7.73/1.49  --dbg_out_stat                          false
% 7.73/1.49  ------ Parsing...
% 7.73/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  ------ Proving...
% 7.73/1.49  ------ Problem Properties 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  clauses                                 31
% 7.73/1.49  conjectures                             3
% 7.73/1.49  EPR                                     1
% 7.73/1.49  Horn                                    20
% 7.73/1.49  unary                                   4
% 7.73/1.49  binary                                  3
% 7.73/1.49  lits                                    141
% 7.73/1.49  lits eq                                 11
% 7.73/1.49  fd_pure                                 0
% 7.73/1.49  fd_pseudo                               0
% 7.73/1.49  fd_cond                                 0
% 7.73/1.49  fd_pseudo_cond                          8
% 7.73/1.49  AC symbols                              0
% 7.73/1.49  
% 7.73/1.49  ------ Schedule dynamic 5 is on 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  Current options:
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    --mode clausify
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.49  --prep_def_merge_mbd                    true
% 7.73/1.49  --prep_def_merge_tr_red                 false
% 7.73/1.49  --prep_def_merge_tr_cl                  false
% 7.73/1.49  --smt_preprocessing                     true
% 7.73/1.49  --smt_ac_axioms                         fast
% 7.73/1.49  --preprocessed_out                      false
% 7.73/1.49  --preprocessed_stats                    false
% 7.73/1.49  
% 7.73/1.49  ------ Abstraction refinement Options
% 7.73/1.49  
% 7.73/1.49  --abstr_ref                             []
% 7.73/1.49  --abstr_ref_prep                        false
% 7.73/1.49  --abstr_ref_until_sat                   false
% 7.73/1.49  --abstr_ref_sig_restrict                funpre
% 7.73/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.49  --abstr_ref_under                       []
% 7.73/1.49  
% 7.73/1.49  ------ SAT Options
% 7.73/1.49  
% 7.73/1.49  --sat_mode                              false
% 7.73/1.49  --sat_fm_restart_options                ""
% 7.73/1.49  --sat_gr_def                            false
% 7.73/1.49  --sat_epr_types                         true
% 7.73/1.49  --sat_non_cyclic_types                  false
% 7.73/1.49  --sat_finite_models                     false
% 7.73/1.49  --sat_fm_lemmas                         false
% 7.73/1.49  --sat_fm_prep                           false
% 7.73/1.49  --sat_fm_uc_incr                        true
% 7.73/1.49  --sat_out_model                         small
% 7.73/1.49  --sat_out_clauses                       false
% 7.73/1.49  
% 7.73/1.49  ------ QBF Options
% 7.73/1.49  
% 7.73/1.49  --qbf_mode                              false
% 7.73/1.49  --qbf_elim_univ                         false
% 7.73/1.49  --qbf_dom_inst                          none
% 7.73/1.49  --qbf_dom_pre_inst                      false
% 7.73/1.49  --qbf_sk_in                             false
% 7.73/1.49  --qbf_pred_elim                         true
% 7.73/1.49  --qbf_split                             512
% 7.73/1.49  
% 7.73/1.49  ------ BMC1 Options
% 7.73/1.49  
% 7.73/1.49  --bmc1_incremental                      false
% 7.73/1.49  --bmc1_axioms                           reachable_all
% 7.73/1.49  --bmc1_min_bound                        0
% 7.73/1.49  --bmc1_max_bound                        -1
% 7.73/1.49  --bmc1_max_bound_default                -1
% 7.73/1.49  --bmc1_symbol_reachability              true
% 7.73/1.49  --bmc1_property_lemmas                  false
% 7.73/1.49  --bmc1_k_induction                      false
% 7.73/1.49  --bmc1_non_equiv_states                 false
% 7.73/1.49  --bmc1_deadlock                         false
% 7.73/1.49  --bmc1_ucm                              false
% 7.73/1.49  --bmc1_add_unsat_core                   none
% 7.73/1.49  --bmc1_unsat_core_children              false
% 7.73/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.49  --bmc1_out_stat                         full
% 7.73/1.49  --bmc1_ground_init                      false
% 7.73/1.49  --bmc1_pre_inst_next_state              false
% 7.73/1.49  --bmc1_pre_inst_state                   false
% 7.73/1.49  --bmc1_pre_inst_reach_state             false
% 7.73/1.49  --bmc1_out_unsat_core                   false
% 7.73/1.49  --bmc1_aig_witness_out                  false
% 7.73/1.49  --bmc1_verbose                          false
% 7.73/1.49  --bmc1_dump_clauses_tptp                false
% 7.73/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.49  --bmc1_dump_file                        -
% 7.73/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.49  --bmc1_ucm_extend_mode                  1
% 7.73/1.49  --bmc1_ucm_init_mode                    2
% 7.73/1.49  --bmc1_ucm_cone_mode                    none
% 7.73/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.49  --bmc1_ucm_relax_model                  4
% 7.73/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.49  --bmc1_ucm_layered_model                none
% 7.73/1.49  --bmc1_ucm_max_lemma_size               10
% 7.73/1.49  
% 7.73/1.49  ------ AIG Options
% 7.73/1.49  
% 7.73/1.49  --aig_mode                              false
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation Options
% 7.73/1.49  
% 7.73/1.49  --instantiation_flag                    true
% 7.73/1.49  --inst_sos_flag                         false
% 7.73/1.49  --inst_sos_phase                        true
% 7.73/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel_side                     none
% 7.73/1.49  --inst_solver_per_active                1400
% 7.73/1.49  --inst_solver_calls_frac                1.
% 7.73/1.49  --inst_passive_queue_type               priority_queues
% 7.73/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.49  --inst_passive_queues_freq              [25;2]
% 7.73/1.49  --inst_dismatching                      true
% 7.73/1.49  --inst_eager_unprocessed_to_passive     true
% 7.73/1.49  --inst_prop_sim_given                   true
% 7.73/1.49  --inst_prop_sim_new                     false
% 7.73/1.49  --inst_subs_new                         false
% 7.73/1.49  --inst_eq_res_simp                      false
% 7.73/1.49  --inst_subs_given                       false
% 7.73/1.49  --inst_orphan_elimination               true
% 7.73/1.49  --inst_learning_loop_flag               true
% 7.73/1.49  --inst_learning_start                   3000
% 7.73/1.49  --inst_learning_factor                  2
% 7.73/1.49  --inst_start_prop_sim_after_learn       3
% 7.73/1.49  --inst_sel_renew                        solver
% 7.73/1.49  --inst_lit_activity_flag                true
% 7.73/1.49  --inst_restr_to_given                   false
% 7.73/1.49  --inst_activity_threshold               500
% 7.73/1.49  --inst_out_proof                        true
% 7.73/1.49  
% 7.73/1.49  ------ Resolution Options
% 7.73/1.49  
% 7.73/1.49  --resolution_flag                       false
% 7.73/1.49  --res_lit_sel                           adaptive
% 7.73/1.49  --res_lit_sel_side                      none
% 7.73/1.49  --res_ordering                          kbo
% 7.73/1.49  --res_to_prop_solver                    active
% 7.73/1.49  --res_prop_simpl_new                    false
% 7.73/1.49  --res_prop_simpl_given                  true
% 7.73/1.49  --res_passive_queue_type                priority_queues
% 7.73/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.49  --res_passive_queues_freq               [15;5]
% 7.73/1.49  --res_forward_subs                      full
% 7.73/1.49  --res_backward_subs                     full
% 7.73/1.49  --res_forward_subs_resolution           true
% 7.73/1.49  --res_backward_subs_resolution          true
% 7.73/1.49  --res_orphan_elimination                true
% 7.73/1.49  --res_time_limit                        2.
% 7.73/1.49  --res_out_proof                         true
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Options
% 7.73/1.49  
% 7.73/1.49  --superposition_flag                    true
% 7.73/1.49  --sup_passive_queue_type                priority_queues
% 7.73/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.49  --demod_completeness_check              fast
% 7.73/1.49  --demod_use_ground                      true
% 7.73/1.49  --sup_to_prop_solver                    passive
% 7.73/1.49  --sup_prop_simpl_new                    true
% 7.73/1.49  --sup_prop_simpl_given                  true
% 7.73/1.49  --sup_fun_splitting                     false
% 7.73/1.49  --sup_smt_interval                      50000
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Simplification Setup
% 7.73/1.49  
% 7.73/1.49  --sup_indices_passive                   []
% 7.73/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_full_bw                           [BwDemod]
% 7.73/1.49  --sup_immed_triv                        [TrivRules]
% 7.73/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_immed_bw_main                     []
% 7.73/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.49  
% 7.73/1.49  ------ Combination Options
% 7.73/1.49  
% 7.73/1.49  --comb_res_mult                         3
% 7.73/1.49  --comb_sup_mult                         2
% 7.73/1.49  --comb_inst_mult                        10
% 7.73/1.49  
% 7.73/1.49  ------ Debug Options
% 7.73/1.49  
% 7.73/1.49  --dbg_backtrace                         false
% 7.73/1.49  --dbg_dump_prop_clauses                 false
% 7.73/1.49  --dbg_dump_prop_clauses_file            -
% 7.73/1.49  --dbg_out_stat                          false
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS status Theorem for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  fof(f26,plain,(
% 7.73/1.49    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))))),
% 7.73/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.73/1.49  
% 7.73/1.49  fof(f30,plain,(
% 7.73/1.49    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0)))),
% 7.73/1.49    inference(nnf_transformation,[],[f26])).
% 7.73/1.49  
% 7.73/1.49  fof(f31,plain,(
% 7.73/1.49    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X5] : (! [X6] : (? [X7] : (! [X8] : (r1_orders_2(X0,X7,X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,X7) & r1_orders_2(X0,X5,X7) & m1_subset_1(X7,u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 7.73/1.49    inference(rectify,[],[f30])).
% 7.73/1.49  
% 7.73/1.49  fof(f35,plain,(
% 7.73/1.49    ! [X6,X5,X0] : (? [X7] : (! [X8] : (r1_orders_2(X0,X7,X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,X7) & r1_orders_2(X0,X5,X7) & m1_subset_1(X7,u1_struct_0(X0))) => (! [X8] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,sK5(X0,X5,X6)) & r1_orders_2(X0,X5,sK5(X0,X5,X6)) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f34,plain,(
% 7.73/1.49    ( ! [X2,X1] : (! [X3,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK4(X0,X3)) & r1_orders_2(X0,X2,sK4(X0,X3)) & r1_orders_2(X0,X1,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f33,plain,(
% 7.73/1.49    ( ! [X1] : (! [X0] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,sK3(X0),X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,sK3(X0),X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f32,plain,(
% 7.73/1.49    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,sK2(X0),X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,sK2(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f36,plain,(
% 7.73/1.49    ! [X0] : ((sP0(X0) | ((! [X3] : ((~r1_orders_2(X0,X3,sK4(X0,X3)) & r1_orders_2(X0,sK3(X0),sK4(X0,X3)) & r1_orders_2(X0,sK2(X0),sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,sK3(X0),X3) | ~r1_orders_2(X0,sK2(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X5] : (! [X6] : ((! [X8] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,sK5(X0,X5,X6)) & r1_orders_2(X0,X5,sK5(X0,X5,X6)) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f31,f35,f34,f33,f32])).
% 7.73/1.49  
% 7.73/1.49  fof(f58,plain,(
% 7.73/1.49    ( ! [X6,X0,X8,X5] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f36])).
% 7.73/1.49  
% 7.73/1.49  fof(f55,plain,(
% 7.73/1.49    ( ! [X6,X0,X5] : (m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f36])).
% 7.73/1.49  
% 7.73/1.49  fof(f57,plain,(
% 7.73/1.49    ( ! [X6,X0,X5] : (r1_orders_2(X0,X6,sK5(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f36])).
% 7.73/1.49  
% 7.73/1.49  fof(f4,axiom,(
% 7.73/1.49    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f16,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f4])).
% 7.73/1.49  
% 7.73/1.49  fof(f17,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f16])).
% 7.73/1.49  
% 7.73/1.49  fof(f37,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f17])).
% 7.73/1.49  
% 7.73/1.49  fof(f38,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f39,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(rectify,[],[f38])).
% 7.73/1.49  
% 7.73/1.49  fof(f40,plain,(
% 7.73/1.49    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f41,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 7.73/1.49  
% 7.73/1.49  fof(f72,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f41])).
% 7.73/1.49  
% 7.73/1.49  fof(f2,axiom,(
% 7.73/1.49    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f12,plain,(
% 7.73/1.49    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f2])).
% 7.73/1.49  
% 7.73/1.49  fof(f13,plain,(
% 7.73/1.49    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 7.73/1.49    inference(flattening,[],[f12])).
% 7.73/1.49  
% 7.73/1.49  fof(f52,plain,(
% 7.73/1.49    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f13])).
% 7.73/1.49  
% 7.73/1.49  fof(f8,conjecture,(
% 7.73/1.49    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f9,negated_conjecture,(
% 7.73/1.49    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 7.73/1.49    inference(negated_conjecture,[],[f8])).
% 7.73/1.49  
% 7.73/1.49  fof(f24,plain,(
% 7.73/1.49    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f9])).
% 7.73/1.49  
% 7.73/1.49  fof(f25,plain,(
% 7.73/1.49    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 7.73/1.49    inference(flattening,[],[f24])).
% 7.73/1.49  
% 7.73/1.49  fof(f49,plain,(
% 7.73/1.49    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK10)) != X1 & m1_subset_1(sK10,u1_struct_0(X0)))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f48,plain,(
% 7.73/1.49    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK9,k13_lattice3(X0,sK9,X2)) != sK9 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f47,plain,(
% 7.73/1.49    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK8,X1,k13_lattice3(sK8,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK8))) & m1_subset_1(X1,u1_struct_0(sK8))) & l1_orders_2(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v3_orders_2(sK8))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f50,plain,(
% 7.73/1.49    ((k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 & m1_subset_1(sK10,u1_struct_0(sK8))) & m1_subset_1(sK9,u1_struct_0(sK8))) & l1_orders_2(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v3_orders_2(sK8)),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f25,f49,f48,f47])).
% 7.73/1.49  
% 7.73/1.49  fof(f83,plain,(
% 7.73/1.49    v5_orders_2(sK8)),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f84,plain,(
% 7.73/1.49    v1_lattice3(sK8)),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f86,plain,(
% 7.73/1.49    l1_orders_2(sK8)),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f69,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f41])).
% 7.73/1.49  
% 7.73/1.49  fof(f70,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f41])).
% 7.73/1.49  
% 7.73/1.49  fof(f5,axiom,(
% 7.73/1.49    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f18,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f5])).
% 7.73/1.49  
% 7.73/1.49  fof(f19,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f18])).
% 7.73/1.49  
% 7.73/1.49  fof(f42,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f19])).
% 7.73/1.49  
% 7.73/1.49  fof(f43,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f42])).
% 7.73/1.49  
% 7.73/1.49  fof(f44,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(rectify,[],[f43])).
% 7.73/1.49  
% 7.73/1.49  fof(f45,plain,(
% 7.73/1.49    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f46,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 7.73/1.49  
% 7.73/1.49  fof(f77,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f46])).
% 7.73/1.49  
% 7.73/1.49  fof(f85,plain,(
% 7.73/1.49    v2_lattice3(sK8)),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f79,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f46])).
% 7.73/1.49  
% 7.73/1.49  fof(f56,plain,(
% 7.73/1.49    ( ! [X6,X0,X5] : (r1_orders_2(X0,X5,sK5(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f36])).
% 7.73/1.49  
% 7.73/1.49  fof(f71,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f41])).
% 7.73/1.49  
% 7.73/1.49  fof(f6,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f20,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f6])).
% 7.73/1.49  
% 7.73/1.49  fof(f21,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 7.73/1.49    inference(flattening,[],[f20])).
% 7.73/1.49  
% 7.73/1.49  fof(f80,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f21])).
% 7.73/1.49  
% 7.73/1.49  fof(f7,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f22,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f7])).
% 7.73/1.49  
% 7.73/1.49  fof(f23,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 7.73/1.49    inference(flattening,[],[f22])).
% 7.73/1.49  
% 7.73/1.49  fof(f81,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f23])).
% 7.73/1.49  
% 7.73/1.49  fof(f1,axiom,(
% 7.73/1.49    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f10,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f1])).
% 7.73/1.49  
% 7.73/1.49  fof(f11,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f10])).
% 7.73/1.49  
% 7.73/1.49  fof(f51,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f11])).
% 7.73/1.49  
% 7.73/1.49  fof(f82,plain,(
% 7.73/1.49    v3_orders_2(sK8)),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f89,plain,(
% 7.73/1.49    k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f27,plain,(
% 7.73/1.49    ! [X0] : ((v1_lattice3(X0) <=> sP0(X0)) | ~sP1(X0))),
% 7.73/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.73/1.49  
% 7.73/1.49  fof(f29,plain,(
% 7.73/1.49    ! [X0] : (((v1_lattice3(X0) | ~sP0(X0)) & (sP0(X0) | ~v1_lattice3(X0))) | ~sP1(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f27])).
% 7.73/1.49  
% 7.73/1.49  fof(f53,plain,(
% 7.73/1.49    ( ! [X0] : (sP0(X0) | ~v1_lattice3(X0) | ~sP1(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f29])).
% 7.73/1.49  
% 7.73/1.49  fof(f3,axiom,(
% 7.73/1.49    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f14,plain,(
% 7.73/1.49    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f3])).
% 7.73/1.49  
% 7.73/1.49  fof(f15,plain,(
% 7.73/1.49    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.73/1.49    inference(flattening,[],[f14])).
% 7.73/1.49  
% 7.73/1.49  fof(f28,plain,(
% 7.73/1.49    ! [X0] : (sP1(X0) | ~l1_orders_2(X0))),
% 7.73/1.49    inference(definition_folding,[],[f15,f27,f26])).
% 7.73/1.49  
% 7.73/1.49  fof(f65,plain,(
% 7.73/1.49    ( ! [X0] : (sP1(X0) | ~l1_orders_2(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f28])).
% 7.73/1.49  
% 7.73/1.49  fof(f88,plain,(
% 7.73/1.49    m1_subset_1(sK10,u1_struct_0(sK8))),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f87,plain,(
% 7.73/1.49    m1_subset_1(sK9,u1_struct_0(sK8))),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | r1_orders_2(X0,sK5(X0,X3,X1),X2)
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ sP0(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2943,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0_52,X0_53,X1_53)
% 7.73/1.49      | ~ r1_orders_2(X0_52,X2_53,X1_53)
% 7.73/1.49      | r1_orders_2(X0_52,sK5(X0_52,X2_53,X0_53),X1_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 7.73/1.49      | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
% 7.73/1.49      | ~ sP0(X0_52) ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_15051,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 7.73/1.49      | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),X1_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK10,X1_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ sP0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2943]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_22602,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X1_53)))
% 7.73/1.49      | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X1_53)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X1_53)))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X1_53)),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ sP0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_15051]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_22604,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK5(sK8,sK10,sK9),sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
% 7.73/1.49      | ~ m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | ~ sP0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_22602]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2953,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0_52,X0_53,X1_53)
% 7.73/1.49      | r1_orders_2(X0_52,X2_53,X3_53)
% 7.73/1.49      | X2_53 != X0_53
% 7.73/1.49      | X3_53 != X1_53 ),
% 7.73/1.49      theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_8182,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 7.73/1.49      | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) != X1_53
% 7.73/1.49      | sK9 != X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2953]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11782,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X1_53))
% 7.73/1.49      | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X1_53)
% 7.73/1.49      | sK9 != X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_8182]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11785,plain,
% 7.73/1.49      ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53)
% 7.73/1.49      | sK9 != X1_53
% 7.73/1.49      | r1_orders_2(sK8,X1_53,sK5(sK8,sK10,X0_53)) != iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_11782]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11787,plain,
% 7.73/1.49      ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,sK9)
% 7.73/1.49      | sK9 != sK9
% 7.73/1.49      | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_11785]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2954,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0_53,X0_54)
% 7.73/1.49      | m1_subset_1(X1_53,X0_54)
% 7.73/1.49      | X1_53 != X0_53 ),
% 7.73/1.49      theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3875,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | X1_53 != X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2954]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4376,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) != X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_3875]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11774,plain,
% 7.73/1.49      ( m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4376]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11775,plain,
% 7.73/1.49      ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53)
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
% 7.73/1.49      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_11774]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11777,plain,
% 7.73/1.49      ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,sK9)
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
% 7.73/1.49      | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_11775]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_13,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.73/1.49      | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
% 7.73/1.49      | ~ sP0(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2940,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 7.73/1.49      | m1_subset_1(sK5(X0_52,X1_53,X0_53),u1_struct_0(X0_52))
% 7.73/1.49      | ~ sP0(X0_52) ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9365,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ sP0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2940]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9366,plain,
% 7.73/1.49      ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) = iProver_top
% 7.73/1.49      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | sP0(sK8) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_9365]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9368,plain,
% 7.73/1.49      ( m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) = iProver_top
% 7.73/1.49      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | sP0(sK8) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_9366]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9367,plain,
% 7.73/1.49      ( m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | ~ sP0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_9365]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11,plain,
% 7.73/1.49      ( r1_orders_2(X0,X1,sK5(X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ sP0(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2942,plain,
% 7.73/1.49      ( r1_orders_2(X0_52,X0_53,sK5(X0_52,X1_53,X0_53))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 7.73/1.49      | ~ sP0(X0_52) ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7021,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | ~ sP0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2942]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7024,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) = iProver_top
% 7.73/1.49      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | sP0(sK8) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_7021]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_15,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1,plain,
% 7.73/1.49      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_258,plain,
% 7.73/1.49      ( ~ v1_lattice3(X0)
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_15,c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_259,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_258]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_37,negated_conjecture,
% 7.73/1.49      ( v5_orders_2(sK8) ),
% 7.73/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_782,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2
% 7.73/1.49      | sK8 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_259,c_37]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_783,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X1,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | ~ v1_lattice3(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8)
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_782]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_36,negated_conjecture,
% 7.73/1.49      ( v1_lattice3(sK8) ),
% 7.73/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_34,negated_conjecture,
% 7.73/1.49      ( l1_orders_2(sK8) ),
% 7.73/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_787,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X1,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_783,c_36,c_34]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_788,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X1,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_787]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2927,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,X1_53,sK6(sK8,X0_53,X2_53,X1_53))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0_53,X2_53) = X1_53 ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_788]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4921,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,X0_53))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK10,X0_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,X0_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2927]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6867,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4921]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6880,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK5(sK8,sK10,sK9),sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6867]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_18,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | m1_subset_1(sK6(X0,X1,X3,X2),u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_239,plain,
% 7.73/1.49      ( ~ v1_lattice3(X0)
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | m1_subset_1(sK6(X0,X1,X3,X2),u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_18,c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_240,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | m1_subset_1(sK6(X0,X1,X3,X2),u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_239]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_877,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | m1_subset_1(sK6(X0,X1,X3,X2),u1_struct_0(X0))
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2
% 7.73/1.49      | sK8 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_240,c_37]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_878,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | m1_subset_1(sK6(sK8,X0,X2,X1),u1_struct_0(sK8))
% 7.73/1.49      | ~ v1_lattice3(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8)
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_877]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_882,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | m1_subset_1(sK6(sK8,X0,X2,X1),u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_878,c_36,c_34]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_883,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | m1_subset_1(sK6(sK8,X0,X2,X1),u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_882]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2924,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 7.73/1.49      | m1_subset_1(sK6(sK8,X0_53,X2_53,X1_53),u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0_53,X2_53) = X1_53 ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_883]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4924,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK10,X0_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,X0_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | m1_subset_1(sK6(sK8,sK9,sK10,X0_53),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2924]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6868,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4924]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6876,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
% 7.73/1.49      | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6868]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | r1_orders_2(X0,X1,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_246,plain,
% 7.73/1.49      ( ~ v1_lattice3(X0)
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | r1_orders_2(X0,X1,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_17,c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_247,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | r1_orders_2(X0,X1,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_246]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_848,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | r1_orders_2(X0,X1,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2
% 7.73/1.49      | sK8 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_247,c_37]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_849,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | r1_orders_2(sK8,X0,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | ~ v1_lattice3(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8)
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_848]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_851,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | r1_orders_2(sK8,X0,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_849,c_36,c_34]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_852,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | r1_orders_2(sK8,X0,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_851]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2925,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 7.73/1.49      | r1_orders_2(sK8,X0_53,sK6(sK8,X0_53,X2_53,X1_53))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0_53,X2_53) = X1_53 ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_852]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4923,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK10,X0_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,X0_53)
% 7.73/1.49      | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,X0_53))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2925]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6869,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4923]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6872,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
% 7.73/1.49      | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6869]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_24,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X1,X3)
% 7.73/1.49      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ v2_lattice3(X0)
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k11_lattice3(X0,X3,X2) = X1 ),
% 7.73/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_35,negated_conjecture,
% 7.73/1.49      ( v2_lattice3(sK8) ),
% 7.73/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_612,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X1,X3)
% 7.73/1.49      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k11_lattice3(X0,X3,X2) = X1
% 7.73/1.49      | sK8 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_613,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0,X2)
% 7.73/1.49      | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ v5_orders_2(sK8)
% 7.73/1.49      | v2_struct_0(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8)
% 7.73/1.49      | k11_lattice3(sK8,X1,X2) = X0 ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_612]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_122,plain,
% 7.73/1.49      ( ~ v1_lattice3(sK8) | ~ v2_struct_0(sK8) | ~ l1_orders_2(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_617,plain,
% 7.73/1.49      ( ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0,X2)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | k11_lattice3(sK8,X1,X2) = X0 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_613,c_37,c_36,c_34,c_122]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_618,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0,X2)
% 7.73/1.49      | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | k11_lattice3(sK8,X1,X2) = X0 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_617]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2931,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 7.73/1.49      | r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X1_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 7.73/1.49      | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_618]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6836,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK7(sK8,X0_53,k10_lattice3(sK8,sK9,sK10),sK9),X0_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,X0_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = sK9 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2931]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6852,plain,
% 7.73/1.49      ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = sK9
% 7.73/1.49      | r1_orders_2(sK8,sK7(sK8,X0_53,k10_lattice3(sK8,sK9,sK10),sK9),X0_53) = iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,X0_53) != iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != iProver_top
% 7.73/1.49      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_6836]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6854,plain,
% 7.73/1.49      ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = sK9
% 7.73/1.49      | r1_orders_2(sK8,sK7(sK8,sK9,k10_lattice3(sK8,sK9,sK10),sK9),sK9) = iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,sK9) != iProver_top
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6852]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_22,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X1,X3)
% 7.73/1.49      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ v2_lattice3(X0)
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k11_lattice3(X0,X3,X2) = X1 ),
% 7.73/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_674,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X1,X3)
% 7.73/1.49      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k11_lattice3(X0,X3,X2) = X1
% 7.73/1.49      | sK8 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_22,c_35]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_675,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0,X2)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ v5_orders_2(sK8)
% 7.73/1.49      | v2_struct_0(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8)
% 7.73/1.49      | k11_lattice3(sK8,X1,X2) = X0 ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_674]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_679,plain,
% 7.73/1.49      ( ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0,X2)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | k11_lattice3(sK8,X1,X2) = X0 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_675,c_37,c_36,c_34,c_122]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_680,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0,X2)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | k11_lattice3(sK8,X1,X2) = X0 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_679]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2929,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X0_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 7.73/1.49      | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_680]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6838,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK7(sK8,X0_53,k10_lattice3(sK8,sK9,sK10),sK9),sK9)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,X0_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = sK9 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2929]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6844,plain,
% 7.73/1.49      ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = sK9
% 7.73/1.49      | r1_orders_2(sK8,sK7(sK8,X0_53,k10_lattice3(sK8,sK9,sK10),sK9),sK9) != iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,X0_53) != iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != iProver_top
% 7.73/1.49      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_6838]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6846,plain,
% 7.73/1.49      ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = sK9
% 7.73/1.49      | r1_orders_2(sK8,sK7(sK8,sK9,k10_lattice3(sK8,sK9,sK10),sK9),sK9) != iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != iProver_top
% 7.73/1.49      | r1_orders_2(sK8,sK9,sK9) != iProver_top
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6844]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2952,plain,
% 7.73/1.49      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 7.73/1.49      theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4269,plain,
% 7.73/1.49      ( k11_lattice3(sK8,X0_53,X1_53) != X2_53
% 7.73/1.49      | sK9 != X2_53
% 7.73/1.49      | sK9 = k11_lattice3(sK8,X0_53,X1_53) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2952]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6183,plain,
% 7.73/1.49      ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) != X1_53
% 7.73/1.49      | sK9 != X1_53
% 7.73/1.49      | sK9 = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4269]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6184,plain,
% 7.73/1.49      ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != sK9
% 7.73/1.49      | sK9 = k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | sK9 != sK9 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6183]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12,plain,
% 7.73/1.49      ( r1_orders_2(X0,X1,sK5(X0,X1,X2))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ sP0(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2941,plain,
% 7.73/1.49      ( r1_orders_2(X0_52,X0_53,sK5(X0_52,X0_53,X1_53))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 7.73/1.49      | ~ sP0(X0_52) ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5459,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ sP0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2941]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5465,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | ~ sP0(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_5459]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_16,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_253,plain,
% 7.73/1.49      ( ~ v1_lattice3(X0)
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_16,c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_254,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v5_orders_2(X0)
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_253]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_815,plain,
% 7.73/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.73/1.49      | ~ r1_orders_2(X0,X3,X2)
% 7.73/1.49      | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.49      | ~ v1_lattice3(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | k10_lattice3(X0,X1,X3) = X2
% 7.73/1.49      | sK8 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_254,c_37]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_816,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | r1_orders_2(sK8,X2,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | ~ v1_lattice3(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8)
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_815]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_820,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | r1_orders_2(sK8,X2,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_816,c_36,c_34]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_821,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0,X1)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2,X1)
% 7.73/1.49      | r1_orders_2(sK8,X2,sK6(sK8,X0,X2,X1))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0,X2) = X1 ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_820]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2926,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 7.73/1.49      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 7.73/1.49      | r1_orders_2(sK8,X2_53,sK6(sK8,X0_53,X2_53,X1_53))
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,X0_53,X2_53) = X1_53 ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_821]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4922,plain,
% 7.73/1.49      ( ~ r1_orders_2(sK8,sK10,X0_53)
% 7.73/1.49      | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,X0_53))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,X0_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2926]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5458,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4922]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5461,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9))
% 7.73/1.49      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9))
% 7.73/1.49      | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_5458]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3951,plain,
% 7.73/1.49      ( k12_lattice3(sK8,X0_53,X1_53) != X2_53
% 7.73/1.49      | sK9 != X2_53
% 7.73/1.49      | sK9 = k12_lattice3(sK8,X0_53,X1_53) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2952]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4154,plain,
% 7.73/1.49      ( k12_lattice3(sK8,X0_53,X1_53) != k11_lattice3(sK8,X0_53,X1_53)
% 7.73/1.49      | sK9 = k12_lattice3(sK8,X0_53,X1_53)
% 7.73/1.49      | sK9 != k11_lattice3(sK8,X0_53,X1_53) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_3951]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4997,plain,
% 7.73/1.49      ( k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) != k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | sK9 = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | sK9 != k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4154]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4998,plain,
% 7.73/1.49      ( k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | sK9 = k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | sK9 != k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4997]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_29,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.73/1.49      | ~ v2_lattice3(X1)
% 7.73/1.49      | ~ v5_orders_2(X1)
% 7.73/1.49      | ~ l1_orders_2(X1)
% 7.73/1.49      | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2) ),
% 7.73/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_707,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.73/1.49      | ~ v5_orders_2(X1)
% 7.73/1.49      | ~ l1_orders_2(X1)
% 7.73/1.49      | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2)
% 7.73/1.49      | sK8 != X1 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_35]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_708,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ v5_orders_2(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8)
% 7.73/1.49      | k12_lattice3(sK8,X0,X1) = k11_lattice3(sK8,X0,X1) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_707]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_712,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | k12_lattice3(sK8,X0,X1) = k11_lattice3(sK8,X0,X1) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_708,c_37,c_34]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_713,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | k12_lattice3(sK8,X1,X0) = k11_lattice3(sK8,X1,X0) ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_712]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2928,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | k12_lattice3(sK8,X1_53,X0_53) = k11_lattice3(sK8,X1_53,X0_53) ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_713]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4943,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 7.73/1.49      | k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2928]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4948,plain,
% 7.73/1.49      ( k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_4943]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4950,plain,
% 7.73/1.49      ( k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 7.73/1.49      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4948]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3857,plain,
% 7.73/1.49      ( X0_53 != X1_53
% 7.73/1.49      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != X1_53
% 7.73/1.49      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2952]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4002,plain,
% 7.73/1.49      ( X0_53 != k12_lattice3(sK8,X1_53,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = X0_53
% 7.73/1.49      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,X1_53,k10_lattice3(sK8,sK9,sK10)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_3857]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4003,plain,
% 7.73/1.49      ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = sK9
% 7.73/1.49      | sK9 != k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4002]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_30,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.73/1.49      | ~ v5_orders_2(X1)
% 7.73/1.49      | ~ v1_lattice3(X1)
% 7.73/1.49      | ~ l1_orders_2(X1)
% 7.73/1.49      | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2) ),
% 7.73/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_987,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.73/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.73/1.49      | ~ v1_lattice3(X1)
% 7.73/1.49      | ~ l1_orders_2(X1)
% 7.73/1.49      | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2)
% 7.73/1.49      | sK8 != X1 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_30,c_37]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_988,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | ~ v1_lattice3(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8)
% 7.73/1.49      | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_987]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_992,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_988,c_36,c_34]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_993,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.73/1.49      | k13_lattice3(sK8,X1,X0) = k10_lattice3(sK8,X1,X0) ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_992]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2920,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 7.73/1.49      | k13_lattice3(sK8,X1_53,X0_53) = k10_lattice3(sK8,X1_53,X0_53) ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_993]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3954,plain,
% 7.73/1.49      ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 7.73/1.49      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 7.73/1.49      | k13_lattice3(sK8,sK9,sK10) = k10_lattice3(sK8,sK9,sK10) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2920]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2955,plain,
% 7.73/1.49      ( X0_53 != X1_53
% 7.73/1.49      | X2_53 != X3_53
% 7.73/1.49      | k12_lattice3(X0_52,X0_53,X2_53) = k12_lattice3(X0_52,X1_53,X3_53) ),
% 7.73/1.49      theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3859,plain,
% 7.73/1.49      ( k13_lattice3(sK8,sK9,sK10) != X0_53
% 7.73/1.49      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X1_53,X0_53)
% 7.73/1.49      | sK9 != X1_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2955]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3953,plain,
% 7.73/1.49      ( k13_lattice3(sK8,sK9,sK10) != k10_lattice3(sK8,sK9,sK10)
% 7.73/1.49      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | sK9 != X0_53 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_3859]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3955,plain,
% 7.73/1.49      ( k13_lattice3(sK8,sK9,sK10) != k10_lattice3(sK8,sK9,sK10)
% 7.73/1.49      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 7.73/1.49      | sK9 != sK9 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_3953]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_0,plain,
% 7.73/1.49      ( r1_orders_2(X0,X1,X1)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ v3_orders_2(X0)
% 7.73/1.49      | ~ l1_orders_2(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_38,negated_conjecture,
% 7.73/1.49      ( v3_orders_2(sK8) ),
% 7.73/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_447,plain,
% 7.73/1.49      ( r1_orders_2(X0,X1,X1)
% 7.73/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.73/1.49      | v2_struct_0(X0)
% 7.73/1.49      | ~ l1_orders_2(X0)
% 7.73/1.49      | sK8 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_38]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_448,plain,
% 7.73/1.49      ( r1_orders_2(sK8,X0,X0)
% 7.73/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.73/1.49      | v2_struct_0(sK8)
% 7.73/1.49      | ~ l1_orders_2(sK8) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_447]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_452,plain,
% 7.73/1.49      ( r1_orders_2(sK8,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_448,c_36,c_34,c_122]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2936,plain,
% 7.73/1.49      ( r1_orders_2(sK8,X0_53,X0_53)
% 7.73/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK8)) ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_452]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2981,plain,
% 7.73/1.49      ( r1_orders_2(sK8,X0_53,X0_53) = iProver_top
% 7.73/1.49      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_2936]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2983,plain,
% 7.73/1.49      ( r1_orders_2(sK8,sK9,sK9) = iProver_top
% 7.73/1.49      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2981]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_31,negated_conjecture,
% 7.73/1.49      ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
% 7.73/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2939,negated_conjecture,
% 7.73/1.49      ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
% 7.73/1.49      inference(subtyping,[status(esa)],[c_31]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2951,plain,( X0_53 = X0_53 ),theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2962,plain,
% 7.73/1.49      ( sK9 = sK9 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2951]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3,plain,
% 7.73/1.49      ( ~ sP1(X0) | sP0(X0) | ~ v1_lattice3(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_117,plain,
% 7.73/1.49      ( sP1(X0) != iProver_top
% 7.73/1.49      | sP0(X0) = iProver_top
% 7.73/1.49      | v1_lattice3(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_119,plain,
% 7.73/1.49      ( sP1(sK8) != iProver_top
% 7.73/1.49      | sP0(sK8) = iProver_top
% 7.73/1.49      | v1_lattice3(sK8) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_117]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_118,plain,
% 7.73/1.49      ( ~ sP1(sK8) | sP0(sK8) | ~ v1_lattice3(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_14,plain,
% 7.73/1.49      ( sP1(X0) | ~ l1_orders_2(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_86,plain,
% 7.73/1.49      ( sP1(X0) = iProver_top | l1_orders_2(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_88,plain,
% 7.73/1.49      ( sP1(sK8) = iProver_top | l1_orders_2(sK8) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_86]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_87,plain,
% 7.73/1.49      ( sP1(sK8) | ~ l1_orders_2(sK8) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32,negated_conjecture,
% 7.73/1.49      ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_45,plain,
% 7.73/1.49      ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33,negated_conjecture,
% 7.73/1.49      ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_44,plain,
% 7.73/1.49      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_43,plain,
% 7.73/1.49      ( l1_orders_2(sK8) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_41,plain,
% 7.73/1.49      ( v1_lattice3(sK8) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(contradiction,plain,
% 7.73/1.49      ( $false ),
% 7.73/1.49      inference(minisat,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_22604,c_11787,c_11777,c_9368,c_9367,c_7024,c_7021,
% 7.73/1.49                 c_6880,c_6876,c_6872,c_6854,c_6846,c_6184,c_5465,c_5461,
% 7.73/1.49                 c_4998,c_4950,c_4003,c_3954,c_3955,c_2983,c_2939,c_2962,
% 7.73/1.49                 c_119,c_118,c_88,c_87,c_45,c_32,c_44,c_33,c_43,c_34,
% 7.73/1.49                 c_41,c_36]) ).
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  ------                               Statistics
% 7.73/1.49  
% 7.73/1.49  ------ General
% 7.73/1.49  
% 7.73/1.49  abstr_ref_over_cycles:                  0
% 7.73/1.49  abstr_ref_under_cycles:                 0
% 7.73/1.49  gc_basic_clause_elim:                   0
% 7.73/1.49  forced_gc_time:                         0
% 7.73/1.49  parsing_time:                           0.01
% 7.73/1.49  unif_index_cands_time:                  0.
% 7.73/1.49  unif_index_add_time:                    0.
% 7.73/1.49  orderings_time:                         0.
% 7.73/1.49  out_proof_time:                         0.019
% 7.73/1.49  total_time:                             0.937
% 7.73/1.49  num_of_symbols:                         55
% 7.73/1.49  num_of_terms:                           33084
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing
% 7.73/1.49  
% 7.73/1.49  num_of_splits:                          0
% 7.73/1.49  num_of_split_atoms:                     0
% 7.73/1.49  num_of_reused_defs:                     0
% 7.73/1.49  num_eq_ax_congr_red:                    69
% 7.73/1.49  num_of_sem_filtered_clauses:            1
% 7.73/1.49  num_of_subtypes:                        3
% 7.73/1.49  monotx_restored_types:                  0
% 7.73/1.49  sat_num_of_epr_types:                   0
% 7.73/1.49  sat_num_of_non_cyclic_types:            0
% 7.73/1.49  sat_guarded_non_collapsed_types:        1
% 7.73/1.49  num_pure_diseq_elim:                    0
% 7.73/1.49  simp_replaced_by:                       0
% 7.73/1.49  res_preprocessed:                       145
% 7.73/1.49  prep_upred:                             0
% 7.73/1.49  prep_unflattend:                        39
% 7.73/1.49  smt_new_axioms:                         0
% 7.73/1.49  pred_elim_cands:                        3
% 7.73/1.49  pred_elim:                              7
% 7.73/1.49  pred_elim_cl:                           8
% 7.73/1.49  pred_elim_cycles:                       9
% 7.73/1.49  merged_defs:                            0
% 7.73/1.49  merged_defs_ncl:                        0
% 7.73/1.49  bin_hyper_res:                          0
% 7.73/1.49  prep_cycles:                            4
% 7.73/1.49  pred_elim_time:                         0.026
% 7.73/1.49  splitting_time:                         0.
% 7.73/1.49  sem_filter_time:                        0.
% 7.73/1.49  monotx_time:                            0.
% 7.73/1.49  subtype_inf_time:                       0.
% 7.73/1.49  
% 7.73/1.49  ------ Problem properties
% 7.73/1.49  
% 7.73/1.49  clauses:                                31
% 7.73/1.49  conjectures:                            3
% 7.73/1.49  epr:                                    1
% 7.73/1.49  horn:                                   20
% 7.73/1.49  ground:                                 4
% 7.73/1.49  unary:                                  4
% 7.73/1.49  binary:                                 3
% 7.73/1.49  lits:                                   141
% 7.73/1.49  lits_eq:                                11
% 7.73/1.49  fd_pure:                                0
% 7.73/1.49  fd_pseudo:                              0
% 7.73/1.49  fd_cond:                                0
% 7.73/1.49  fd_pseudo_cond:                         8
% 7.73/1.49  ac_symbols:                             0
% 7.73/1.49  
% 7.73/1.49  ------ Propositional Solver
% 7.73/1.49  
% 7.73/1.49  prop_solver_calls:                      35
% 7.73/1.49  prop_fast_solver_calls:                 2645
% 7.73/1.49  smt_solver_calls:                       0
% 7.73/1.49  smt_fast_solver_calls:                  0
% 7.73/1.49  prop_num_of_clauses:                    9327
% 7.73/1.49  prop_preprocess_simplified:             22964
% 7.73/1.49  prop_fo_subsumed:                       91
% 7.73/1.49  prop_solver_time:                       0.
% 7.73/1.49  smt_solver_time:                        0.
% 7.73/1.49  smt_fast_solver_time:                   0.
% 7.73/1.49  prop_fast_solver_time:                  0.
% 7.73/1.49  prop_unsat_core_time:                   0.004
% 7.73/1.49  
% 7.73/1.49  ------ QBF
% 7.73/1.49  
% 7.73/1.49  qbf_q_res:                              0
% 7.73/1.49  qbf_num_tautologies:                    0
% 7.73/1.49  qbf_prep_cycles:                        0
% 7.73/1.49  
% 7.73/1.49  ------ BMC1
% 7.73/1.49  
% 7.73/1.49  bmc1_current_bound:                     -1
% 7.73/1.49  bmc1_last_solved_bound:                 -1
% 7.73/1.49  bmc1_unsat_core_size:                   -1
% 7.73/1.49  bmc1_unsat_core_parents_size:           -1
% 7.73/1.49  bmc1_merge_next_fun:                    0
% 7.73/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation
% 7.73/1.49  
% 7.73/1.49  inst_num_of_clauses:                    2702
% 7.73/1.49  inst_num_in_passive:                    323
% 7.73/1.49  inst_num_in_active:                     1018
% 7.73/1.49  inst_num_in_unprocessed:                1361
% 7.73/1.49  inst_num_of_loops:                      1125
% 7.73/1.49  inst_num_of_learning_restarts:          0
% 7.73/1.49  inst_num_moves_active_passive:          99
% 7.73/1.49  inst_lit_activity:                      0
% 7.73/1.49  inst_lit_activity_moves:                0
% 7.73/1.49  inst_num_tautologies:                   0
% 7.73/1.49  inst_num_prop_implied:                  0
% 7.73/1.49  inst_num_existing_simplified:           0
% 7.73/1.49  inst_num_eq_res_simplified:             0
% 7.73/1.49  inst_num_child_elim:                    0
% 7.73/1.49  inst_num_of_dismatching_blockings:      1446
% 7.73/1.49  inst_num_of_non_proper_insts:           3630
% 7.73/1.49  inst_num_of_duplicates:                 0
% 7.73/1.49  inst_inst_num_from_inst_to_res:         0
% 7.73/1.49  inst_dismatching_checking_time:         0.
% 7.73/1.49  
% 7.73/1.49  ------ Resolution
% 7.73/1.49  
% 7.73/1.49  res_num_of_clauses:                     0
% 7.73/1.49  res_num_in_passive:                     0
% 7.73/1.49  res_num_in_active:                      0
% 7.73/1.49  res_num_of_loops:                       149
% 7.73/1.49  res_forward_subset_subsumed:            205
% 7.73/1.49  res_backward_subset_subsumed:           0
% 7.73/1.49  res_forward_subsumed:                   0
% 7.73/1.49  res_backward_subsumed:                  0
% 7.73/1.49  res_forward_subsumption_resolution:     0
% 7.73/1.49  res_backward_subsumption_resolution:    0
% 7.73/1.49  res_clause_to_clause_subsumption:       5691
% 7.73/1.49  res_orphan_elimination:                 0
% 7.73/1.49  res_tautology_del:                      300
% 7.73/1.49  res_num_eq_res_simplified:              0
% 7.73/1.49  res_num_sel_changes:                    0
% 7.73/1.49  res_moves_from_active_to_pass:          0
% 7.73/1.49  
% 7.73/1.49  ------ Superposition
% 7.73/1.49  
% 7.73/1.49  sup_time_total:                         0.
% 7.73/1.49  sup_time_generating:                    0.
% 7.73/1.49  sup_time_sim_full:                      0.
% 7.73/1.49  sup_time_sim_immed:                     0.
% 7.73/1.49  
% 7.73/1.49  sup_num_of_clauses:                     506
% 7.73/1.49  sup_num_in_active:                      210
% 7.73/1.49  sup_num_in_passive:                     296
% 7.73/1.49  sup_num_of_loops:                       224
% 7.73/1.49  sup_fw_superposition:                   636
% 7.73/1.49  sup_bw_superposition:                   149
% 7.73/1.49  sup_immediate_simplified:               319
% 7.73/1.49  sup_given_eliminated:                   0
% 7.73/1.49  comparisons_done:                       0
% 7.73/1.49  comparisons_avoided:                    12
% 7.73/1.49  
% 7.73/1.49  ------ Simplifications
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  sim_fw_subset_subsumed:                 225
% 7.73/1.49  sim_bw_subset_subsumed:                 1
% 7.73/1.49  sim_fw_subsumed:                        50
% 7.73/1.49  sim_bw_subsumed:                        0
% 7.73/1.49  sim_fw_subsumption_res:                 2
% 7.73/1.49  sim_bw_subsumption_res:                 0
% 7.73/1.49  sim_tautology_del:                      25
% 7.73/1.49  sim_eq_tautology_del:                   0
% 7.73/1.49  sim_eq_res_simp:                        0
% 7.73/1.49  sim_fw_demodulated:                     0
% 7.73/1.49  sim_bw_demodulated:                     13
% 7.73/1.49  sim_light_normalised:                   68
% 7.73/1.49  sim_joinable_taut:                      0
% 7.73/1.49  sim_joinable_simp:                      0
% 7.73/1.49  sim_ac_normalised:                      0
% 7.73/1.49  sim_smt_subsumption:                    0
% 7.73/1.49  
%------------------------------------------------------------------------------
