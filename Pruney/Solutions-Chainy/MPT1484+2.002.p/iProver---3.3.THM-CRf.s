%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:01 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 695 expanded)
%              Number of clauses        :  160 ( 203 expanded)
%              Number of leaves         :   25 ( 211 expanded)
%              Depth                    :   19
%              Number of atoms          : 1541 (5265 expanded)
%              Number of equality atoms :  268 ( 703 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_orders_2(X0,X4,X2)
                      | ~ r1_orders_2(X0,X4,X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X3,X2)
                  & r1_orders_2(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( r1_orders_2(X0,X8,X7)
                        | ~ r1_orders_2(X0,X8,X6)
                        | ~ r1_orders_2(X0,X8,X5)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X7,X6)
                    & r1_orders_2(X0,X7,X5)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f38,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X8,X7)
              | ~ r1_orders_2(X0,X8,X6)
              | ~ r1_orders_2(X0,X8,X5)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,X8,sK5(X0,X5,X6))
            | ~ r1_orders_2(X0,X8,X6)
            | ~ r1_orders_2(X0,X8,X5)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,sK5(X0,X5,X6),X6)
        & r1_orders_2(X0,sK5(X0,X5,X6),X5)
        & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X3),X3)
        & r1_orders_2(X0,sK4(X0,X3),X2)
        & r1_orders_2(X0,sK4(X0,X3),X1)
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r1_orders_2(X0,X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X2)
              | ~ r1_orders_2(X0,X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_orders_2(X0,X4,sK3(X0))
                & r1_orders_2(X0,X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X3,sK3(X0))
            | ~ r1_orders_2(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r1_orders_2(X0,X4,sK2(X0))
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,X2)
                | ~ r1_orders_2(X0,X3,sK2(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,sK4(X0,X3),X3)
                & r1_orders_2(X0,sK4(X0,X3),sK3(X0))
                & r1_orders_2(X0,sK4(X0,X3),sK2(X0))
                & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,sK3(X0))
              | ~ r1_orders_2(X0,X3,sK2(X0))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK3(X0),u1_struct_0(X0))
          & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,X8,sK5(X0,X5,X6))
                      | ~ r1_orders_2(X0,X8,X6)
                      | ~ r1_orders_2(X0,X8,X5)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,sK5(X0,X5,X6),X6)
                  & r1_orders_2(X0,sK5(X0,X5,X6),X5)
                  & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f34,f38,f37,f36,f35])).

fof(f62,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,X8,sK5(X0,X5,X6))
      | ~ r1_orders_2(X0,X8,X6)
      | ~ r1_orders_2(X0,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK5(X0,X5,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k13_lattice3(X0,k12_lattice3(X0,X1,sK10),sK10) != sK10
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k13_lattice3(X0,k12_lattice3(X0,sK9,X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
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
              ( k13_lattice3(sK8,k12_lattice3(sK8,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(sK8)) )
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & l1_orders_2(sK8)
      & v2_lattice3(sK8)
      & v1_lattice3(sK8)
      & v5_orders_2(sK8)
      & v3_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != sK10
    & m1_subset_1(sK10,u1_struct_0(sK8))
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l1_orders_2(sK8)
    & v2_lattice3(sK8)
    & v1_lattice3(sK8)
    & v5_orders_2(sK8)
    & v3_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f28,f52,f51,f50])).

fof(f87,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK5(X0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,(
    k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != sK10 ),
    inference(cnf_transformation,[],[f53])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X4,X2)
                            & r1_orders_2(X0,X4,X1) )
                         => r1_orders_2(X0,X4,X3) ) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f30,f29])).

fof(f69,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,sK5(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2992,plain,
    ( ~ r1_orders_2(X0_52,X0_53,X1_53)
    | ~ r1_orders_2(X0_52,X0_53,X2_53)
    | r1_orders_2(X0_52,X0_53,sK5(X0_52,X2_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_16915,plain,
    ( ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),X0_53)
    | r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK5(sK8,sK9,X0_53))
    | ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_2992])).

cnf(c_16917,plain,
    ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK5(sK8,sK9,sK10))
    | ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK10)
    | ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK9)
    | ~ m1_subset_1(sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_16915])).

cnf(c_3002,plain,
    ( ~ r1_orders_2(X0_52,X0_53,X1_53)
    | r1_orders_2(X0_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_6375,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | r1_orders_2(sK8,k11_lattice3(sK8,sK9,X2_53),sK10)
    | k11_lattice3(sK8,sK9,X2_53) != X0_53
    | sK10 != X1_53 ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_11451,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),X1_53)
    | k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,X0_53)
    | sK10 != X1_53 ),
    inference(instantiation,[status(thm)],[c_6375])).

cnf(c_11452,plain,
    ( k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,X0_53)
    | sK10 != X1_53
    | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = iProver_top
    | r1_orders_2(sK8,sK5(sK8,sK9,X0_53),X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11451])).

cnf(c_11454,plain,
    ( k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,sK10)
    | sK10 != sK10
    | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = iProver_top
    | r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11452])).

cnf(c_3003,plain,
    ( ~ m1_subset_1(X0_53,X0_54)
    | m1_subset_1(X1_53,X0_54)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_3924,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(X1_53,u1_struct_0(sK8))
    | X1_53 != X0_53 ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_4425,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) != X0_53 ),
    inference(instantiation,[status(thm)],[c_3924])).

cnf(c_11435,plain,
    ( m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,X0_53) ),
    inference(instantiation,[status(thm)],[c_4425])).

cnf(c_11436,plain,
    ( k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,X0_53)
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11435])).

cnf(c_11438,plain,
    ( k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,sK10)
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11436])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2989,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | m1_subset_1(sK5(X0_52,X1_53,X0_53),u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_9416,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_2989])).

cnf(c_9417,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9416])).

cnf(c_9419,plain,
    ( m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9417])).

cnf(c_9418,plain,
    ( m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_9416])).

cnf(c_12,plain,
    ( r1_orders_2(X0,sK5(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2991,plain,
    ( r1_orders_2(X0_52,sK5(X0_52,X0_53,X1_53),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_6851,plain,
    ( r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_2991])).

cnf(c_6854,plain,
    ( r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6851])).

cnf(c_23,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_257,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_2])).

cnf(c_258,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_38,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_831,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_258,c_38])).

cnf(c_832,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_36,negated_conjecture,
    ( v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_836,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_36,c_35])).

cnf(c_837,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_836])).

cnf(c_2976,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | ~ r1_orders_2(sK8,sK7(sK8,X2_53,X1_53,X0_53),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2_53,X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_837])).

cnf(c_4970,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK10)
    | ~ r1_orders_2(sK8,X0_53,sK9)
    | ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,X0_53),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2976])).

cnf(c_6692,plain,
    ( ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK5(sK8,sK9,X0_53))
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
    | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,X0_53) ),
    inference(instantiation,[status(thm)],[c_4970])).

cnf(c_6705,plain,
    ( ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK5(sK8,sK9,sK10))
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
    | ~ m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_6692])).

cnf(c_26,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK7(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_238,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK7(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_2])).

cnf(c_239,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK7(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_926,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK7(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_38])).

cnf(c_927,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,X2,X1,X0),u1_struct_0(sK8))
    | ~ v2_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_931,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,X2,X1,X0),u1_struct_0(sK8))
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_927,c_36,c_35])).

cnf(c_932,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,X2,X1,X0),u1_struct_0(sK8))
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_931])).

cnf(c_2973,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,X2_53,X1_53,X0_53),u1_struct_0(sK8))
    | k11_lattice3(sK8,X2_53,X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_932])).

cnf(c_4973,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK10)
    | ~ r1_orders_2(sK8,X0_53,sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8,sK9,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2973])).

cnf(c_6693,plain,
    ( ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
    | m1_subset_1(sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,X0_53) ),
    inference(instantiation,[status(thm)],[c_4973])).

cnf(c_6701,plain,
    ( ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
    | m1_subset_1(sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_6693])).

cnf(c_25,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_245,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_2])).

cnf(c_246,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_245])).

cnf(c_897,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_246,c_38])).

cnf(c_898,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_897])).

cnf(c_900,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_898,c_36,c_35])).

cnf(c_901,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_900])).

cnf(c_2974,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | r1_orders_2(sK8,sK7(sK8,X2_53,X1_53,X0_53),X2_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2_53,X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_901])).

cnf(c_4972,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK10)
    | ~ r1_orders_2(sK8,X0_53,sK9)
    | r1_orders_2(sK8,sK7(sK8,sK9,sK10,X0_53),sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2974])).

cnf(c_6694,plain,
    ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK9)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
    | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,X0_53) ),
    inference(instantiation,[status(thm)],[c_4972])).

cnf(c_6697,plain,
    ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK9)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
    | ~ m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_6694])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_1,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_302,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_1])).

cnf(c_303,plain,
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
    inference(renaming,[status(thm)],[c_302])).

cnf(c_37,negated_conjecture,
    ( v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_551,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_303,c_37])).

cnf(c_552,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_556,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_38,c_35])).

cnf(c_557,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_556])).

cnf(c_2984,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | ~ r1_orders_2(sK8,X1_53,sK6(sK8,X2_53,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_557])).

cnf(c_6667,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK10)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | ~ r1_orders_2(sK8,sK10,sK6(sK8,k11_lattice3(sK8,sK9,sK10),X0_53,sK10))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = sK10 ),
    inference(instantiation,[status(thm)],[c_2984])).

cnf(c_6683,plain,
    ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = sK10
    | r1_orders_2(sK8,X0_53,sK10) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != iProver_top
    | r1_orders_2(sK8,sK10,sK6(sK8,k11_lattice3(sK8,sK9,sK10),X0_53,sK10)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6667])).

cnf(c_6685,plain,
    ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = sK10
    | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != iProver_top
    | r1_orders_2(sK8,sK10,sK6(sK8,k11_lattice3(sK8,sK9,sK10),sK10,sK10)) != iProver_top
    | r1_orders_2(sK8,sK10,sK10) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6683])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_297,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_1])).

cnf(c_298,plain,
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
    inference(renaming,[status(thm)],[c_297])).

cnf(c_584,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X3) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_298,c_37])).

cnf(c_585,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_589,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_38,c_35])).

cnf(c_590,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_589])).

cnf(c_2983,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | r1_orders_2(sK8,X0_53,sK6(sK8,X2_53,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_590])).

cnf(c_6668,plain,
    ( r1_orders_2(sK8,X0_53,sK6(sK8,k11_lattice3(sK8,sK9,sK10),X0_53,sK10))
    | ~ r1_orders_2(sK8,X0_53,sK10)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = sK10 ),
    inference(instantiation,[status(thm)],[c_2983])).

cnf(c_6679,plain,
    ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = sK10
    | r1_orders_2(sK8,X0_53,sK6(sK8,k11_lattice3(sK8,sK9,sK10),X0_53,sK10)) = iProver_top
    | r1_orders_2(sK8,X0_53,sK10) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6668])).

cnf(c_6681,plain,
    ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = sK10
    | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != iProver_top
    | r1_orders_2(sK8,sK10,sK6(sK8,k11_lattice3(sK8,sK9,sK10),sK10,sK10)) = iProver_top
    | r1_orders_2(sK8,sK10,sK10) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6679])).

cnf(c_3001,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_4318,plain,
    ( k10_lattice3(sK8,X0_53,X1_53) != X2_53
    | sK10 != X2_53
    | sK10 = k10_lattice3(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_3001])).

cnf(c_6050,plain,
    ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) != X1_53
    | sK10 != X1_53
    | sK10 = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) ),
    inference(instantiation,[status(thm)],[c_4318])).

cnf(c_6051,plain,
    ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != sK10
    | sK10 = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_6050])).

cnf(c_13,plain,
    ( r1_orders_2(X0,sK5(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2990,plain,
    ( r1_orders_2(X0_52,sK5(X0_52,X0_53,X1_53),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_5508,plain,
    ( r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_2990])).

cnf(c_5514,plain,
    ( r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_5508])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_252,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_2])).

cnf(c_253,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_864,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_253,c_38])).

cnf(c_865,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_864])).

cnf(c_869,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_865,c_36,c_35])).

cnf(c_870,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_869])).

cnf(c_2975,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | r1_orders_2(sK8,sK7(sK8,X2_53,X1_53,X0_53),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X2_53,X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_870])).

cnf(c_4971,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK10)
    | ~ r1_orders_2(sK8,X0_53,sK9)
    | r1_orders_2(sK8,sK7(sK8,sK9,sK10,X0_53),sK10)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2975])).

cnf(c_5507,plain,
    ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
    | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,X0_53) ),
    inference(instantiation,[status(thm)],[c_4971])).

cnf(c_5510,plain,
    ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
    | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
    | ~ m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_5507])).

cnf(c_4000,plain,
    ( k13_lattice3(sK8,X0_53,X1_53) != X2_53
    | sK10 != X2_53
    | sK10 = k13_lattice3(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_3001])).

cnf(c_4203,plain,
    ( k13_lattice3(sK8,X0_53,X1_53) != k10_lattice3(sK8,X0_53,X1_53)
    | sK10 = k13_lattice3(sK8,X0_53,X1_53)
    | sK10 != k10_lattice3(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_4000])).

cnf(c_5046,plain,
    ( k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) != k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53)
    | sK10 = k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53)
    | sK10 != k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) ),
    inference(instantiation,[status(thm)],[c_4203])).

cnf(c_5047,plain,
    ( k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | sK10 = k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | sK10 != k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) ),
    inference(instantiation,[status(thm)],[c_5046])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_756,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_757,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_757,c_38,c_35])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k13_lattice3(sK8,X1,X0) = k10_lattice3(sK8,X1,X0) ),
    inference(renaming,[status(thm)],[c_761])).

cnf(c_2977,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | k13_lattice3(sK8,X1_53,X0_53) = k10_lattice3(sK8,X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_762])).

cnf(c_4992,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) ),
    inference(instantiation,[status(thm)],[c_2977])).

cnf(c_4997,plain,
    ( k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4992])).

cnf(c_4999,plain,
    ( k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4997])).

cnf(c_3906,plain,
    ( X0_53 != X1_53
    | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != X1_53
    | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_3001])).

cnf(c_4051,plain,
    ( X0_53 != k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X1_53)
    | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = X0_53
    | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X1_53) ),
    inference(instantiation,[status(thm)],[c_3906])).

cnf(c_4052,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = sK10
    | sK10 != k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) ),
    inference(instantiation,[status(thm)],[c_4051])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1036,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_38])).

cnf(c_1037,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | k12_lattice3(sK8,X0,X1) = k11_lattice3(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1036])).

cnf(c_1041,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k12_lattice3(sK8,X0,X1) = k11_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1037,c_36,c_35])).

cnf(c_1042,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k12_lattice3(sK8,X1,X0) = k11_lattice3(sK8,X1,X0) ),
    inference(renaming,[status(thm)],[c_1041])).

cnf(c_2969,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | k12_lattice3(sK8,X1_53,X0_53) = k11_lattice3(sK8,X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_1042])).

cnf(c_4003,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k12_lattice3(sK8,sK9,sK10) = k11_lattice3(sK8,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_2969])).

cnf(c_3005,plain,
    ( X0_53 != X1_53
    | X2_53 != X3_53
    | k13_lattice3(X0_52,X0_53,X2_53) = k13_lattice3(X0_52,X1_53,X3_53) ),
    theory(equality)).

cnf(c_3908,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = k13_lattice3(sK8,X0_53,X1_53)
    | k12_lattice3(sK8,sK9,sK10) != X0_53
    | sK10 != X1_53 ),
    inference(instantiation,[status(thm)],[c_3005])).

cnf(c_4002,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53)
    | k12_lattice3(sK8,sK9,sK10) != k11_lattice3(sK8,sK9,sK10)
    | sK10 != X0_53 ),
    inference(instantiation,[status(thm)],[c_3908])).

cnf(c_4004,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
    | k12_lattice3(sK8,sK9,sK10) != k11_lattice3(sK8,sK9,sK10)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_4002])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_39,negated_conjecture,
    ( v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_496,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_39])).

cnf(c_497,plain,
    ( r1_orders_2(sK8,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_123,plain,
    ( ~ v2_lattice3(sK8)
    | ~ v2_struct_0(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_501,plain,
    ( r1_orders_2(sK8,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_36,c_35,c_123])).

cnf(c_2985,plain,
    ( r1_orders_2(sK8,X0_53,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_501])).

cnf(c_3030,plain,
    ( r1_orders_2(sK8,X0_53,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2985])).

cnf(c_3032,plain,
    ( r1_orders_2(sK8,sK10,sK10) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_32,negated_conjecture,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != sK10 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2988,negated_conjecture,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != sK10 ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_3000,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_3011,plain,
    ( sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_3000])).

cnf(c_4,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_118,plain,
    ( sP1(X0) != iProver_top
    | sP0(X0) = iProver_top
    | v2_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_120,plain,
    ( sP1(sK8) != iProver_top
    | sP0(sK8) = iProver_top
    | v2_lattice3(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_119,plain,
    ( ~ sP1(sK8)
    | sP0(sK8)
    | ~ v2_lattice3(sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( sP1(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_87,plain,
    ( sP1(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_89,plain,
    ( sP1(sK8) = iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_88,plain,
    ( sP1(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_46,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( v2_lattice3(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16917,c_11454,c_11438,c_9419,c_9418,c_6854,c_6851,c_6705,c_6701,c_6697,c_6685,c_6681,c_6051,c_5514,c_5510,c_5047,c_4999,c_4052,c_4003,c_4004,c_3032,c_2988,c_3011,c_120,c_119,c_89,c_88,c_46,c_33,c_45,c_34,c_44,c_35,c_43,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    --mode clausify
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         false
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     num_symb
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       true
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     false
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   []
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_full_bw                           [BwDemod]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  ------ Parsing...
% 3.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  ------ Proving...
% 3.79/0.99  ------ Problem Properties 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  clauses                                 31
% 3.79/0.99  conjectures                             3
% 3.79/0.99  EPR                                     1
% 3.79/0.99  Horn                                    20
% 3.79/0.99  unary                                   4
% 3.79/0.99  binary                                  3
% 3.79/0.99  lits                                    141
% 3.79/0.99  lits eq                                 11
% 3.79/0.99  fd_pure                                 0
% 3.79/0.99  fd_pseudo                               0
% 3.79/0.99  fd_cond                                 0
% 3.79/0.99  fd_pseudo_cond                          8
% 3.79/0.99  AC symbols                              0
% 3.79/0.99  
% 3.79/0.99  ------ Schedule dynamic 5 is on 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  Current options:
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    --mode clausify
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         false
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     none
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       false
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     false
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   []
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_full_bw                           [BwDemod]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS status Theorem for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  fof(f29,plain,(
% 3.79/0.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))))),
% 3.79/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.79/0.99  
% 3.79/0.99  fof(f33,plain,(
% 3.79/0.99    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.79/0.99    inference(nnf_transformation,[],[f29])).
% 3.79/0.99  
% 3.79/0.99  fof(f34,plain,(
% 3.79/0.99    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X5] : (! [X6] : (? [X7] : (! [X8] : (r1_orders_2(X0,X8,X7) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X7,X6) & r1_orders_2(X0,X7,X5) & m1_subset_1(X7,u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.79/0.99    inference(rectify,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f38,plain,(
% 3.79/0.99    ! [X6,X5,X0] : (? [X7] : (! [X8] : (r1_orders_2(X0,X8,X7) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X7,X6) & r1_orders_2(X0,X7,X5) & m1_subset_1(X7,u1_struct_0(X0))) => (! [X8] : (r1_orders_2(X0,X8,sK5(X0,X5,X6)) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,sK5(X0,X5,X6),X6) & r1_orders_2(X0,sK5(X0,X5,X6),X5) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f37,plain,(
% 3.79/0.99    ( ! [X2,X1] : (! [X3,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X3),X3) & r1_orders_2(X0,sK4(X0,X3),X2) & r1_orders_2(X0,sK4(X0,X3),X1) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f36,plain,(
% 3.79/0.99    ( ! [X1] : (! [X0] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,sK3(X0)) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,sK3(X0)) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f35,plain,(
% 3.79/0.99    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,sK2(X0)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,sK2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f39,plain,(
% 3.79/0.99    ! [X0] : ((sP0(X0) | ((! [X3] : ((~r1_orders_2(X0,sK4(X0,X3),X3) & r1_orders_2(X0,sK4(X0,X3),sK3(X0)) & r1_orders_2(X0,sK4(X0,X3),sK2(X0)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,sK3(X0)) | ~r1_orders_2(X0,X3,sK2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X5] : (! [X6] : ((! [X8] : (r1_orders_2(X0,X8,sK5(X0,X5,X6)) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,sK5(X0,X5,X6),X6) & r1_orders_2(X0,sK5(X0,X5,X6),X5) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f34,f38,f37,f36,f35])).
% 3.79/0.99  
% 3.79/0.99  fof(f62,plain,(
% 3.79/0.99    ( ! [X6,X0,X8,X5] : (r1_orders_2(X0,X8,sK5(X0,X5,X6)) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f39])).
% 3.79/0.99  
% 3.79/0.99  fof(f59,plain,(
% 3.79/0.99    ( ! [X6,X0,X5] : (m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f39])).
% 3.79/0.99  
% 3.79/0.99  fof(f61,plain,(
% 3.79/0.99    ( ! [X6,X0,X5] : (r1_orders_2(X0,sK5(X0,X5,X6),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f39])).
% 3.79/0.99  
% 3.79/0.99  fof(f6,axiom,(
% 3.79/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f21,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f6])).
% 3.79/0.99  
% 3.79/0.99  fof(f22,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(flattening,[],[f21])).
% 3.79/0.99  
% 3.79/0.99  fof(f45,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(nnf_transformation,[],[f22])).
% 3.79/0.99  
% 3.79/0.99  fof(f46,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(flattening,[],[f45])).
% 3.79/0.99  
% 3.79/0.99  fof(f47,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(rectify,[],[f46])).
% 3.79/0.99  
% 3.79/0.99  fof(f48,plain,(
% 3.79/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f49,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 3.79/0.99  
% 3.79/0.99  fof(f83,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f49])).
% 3.79/0.99  
% 3.79/0.99  fof(f3,axiom,(
% 3.79/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f15,plain,(
% 3.79/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f3])).
% 3.79/0.99  
% 3.79/0.99  fof(f16,plain,(
% 3.79/0.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 3.79/0.99    inference(flattening,[],[f15])).
% 3.79/0.99  
% 3.79/0.99  fof(f56,plain,(
% 3.79/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f16])).
% 3.79/0.99  
% 3.79/0.99  fof(f9,conjecture,(
% 3.79/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f10,negated_conjecture,(
% 3.79/0.99    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 3.79/0.99    inference(negated_conjecture,[],[f9])).
% 3.79/0.99  
% 3.79/0.99  fof(f27,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f10])).
% 3.79/0.99  
% 3.79/0.99  fof(f28,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 3.79/0.99    inference(flattening,[],[f27])).
% 3.79/0.99  
% 3.79/0.99  fof(f52,plain,(
% 3.79/0.99    ( ! [X0,X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k13_lattice3(X0,k12_lattice3(X0,X1,sK10),sK10) != sK10 & m1_subset_1(sK10,u1_struct_0(X0)))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f51,plain,(
% 3.79/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,sK9,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f50,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k13_lattice3(sK8,k12_lattice3(sK8,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK8))) & m1_subset_1(X1,u1_struct_0(sK8))) & l1_orders_2(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v3_orders_2(sK8))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f53,plain,(
% 3.79/0.99    ((k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != sK10 & m1_subset_1(sK10,u1_struct_0(sK8))) & m1_subset_1(sK9,u1_struct_0(sK8))) & l1_orders_2(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v3_orders_2(sK8)),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f28,f52,f51,f50])).
% 3.79/0.99  
% 3.79/0.99  fof(f87,plain,(
% 3.79/0.99    v5_orders_2(sK8)),
% 3.79/0.99    inference(cnf_transformation,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  fof(f89,plain,(
% 3.79/0.99    v2_lattice3(sK8)),
% 3.79/0.99    inference(cnf_transformation,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  fof(f90,plain,(
% 3.79/0.99    l1_orders_2(sK8)),
% 3.79/0.99    inference(cnf_transformation,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  fof(f80,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f49])).
% 3.79/0.99  
% 3.79/0.99  fof(f81,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f49])).
% 3.79/0.99  
% 3.79/0.99  fof(f5,axiom,(
% 3.79/0.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f19,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f5])).
% 3.79/0.99  
% 3.79/0.99  fof(f20,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(flattening,[],[f19])).
% 3.79/0.99  
% 3.79/0.99  fof(f40,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(nnf_transformation,[],[f20])).
% 3.79/0.99  
% 3.79/0.99  fof(f41,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(flattening,[],[f40])).
% 3.79/0.99  
% 3.79/0.99  fof(f42,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(rectify,[],[f41])).
% 3.79/0.99  
% 3.79/0.99  fof(f43,plain,(
% 3.79/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f44,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 3.79/0.99  
% 3.79/0.99  fof(f76,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f44])).
% 3.79/0.99  
% 3.79/0.99  fof(f2,axiom,(
% 3.79/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f13,plain,(
% 3.79/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f2])).
% 3.79/0.99  
% 3.79/0.99  fof(f14,plain,(
% 3.79/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.79/0.99    inference(flattening,[],[f13])).
% 3.79/0.99  
% 3.79/0.99  fof(f55,plain,(
% 3.79/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f14])).
% 3.79/0.99  
% 3.79/0.99  fof(f88,plain,(
% 3.79/0.99    v1_lattice3(sK8)),
% 3.79/0.99    inference(cnf_transformation,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  fof(f75,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f44])).
% 3.79/0.99  
% 3.79/0.99  fof(f60,plain,(
% 3.79/0.99    ( ! [X6,X0,X5] : (r1_orders_2(X0,sK5(X0,X5,X6),X5) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f39])).
% 3.79/0.99  
% 3.79/0.99  fof(f82,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f49])).
% 3.79/0.99  
% 3.79/0.99  fof(f8,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f25,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f8])).
% 3.79/0.99  
% 3.79/0.99  fof(f26,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.79/0.99    inference(flattening,[],[f25])).
% 3.79/0.99  
% 3.79/0.99  fof(f85,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f26])).
% 3.79/0.99  
% 3.79/0.99  fof(f7,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f23,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f7])).
% 3.79/0.99  
% 3.79/0.99  fof(f24,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.79/0.99    inference(flattening,[],[f23])).
% 3.79/0.99  
% 3.79/0.99  fof(f84,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f24])).
% 3.79/0.99  
% 3.79/0.99  fof(f1,axiom,(
% 3.79/0.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f11,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f1])).
% 3.79/0.99  
% 3.79/0.99  fof(f12,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(flattening,[],[f11])).
% 3.79/0.99  
% 3.79/0.99  fof(f54,plain,(
% 3.79/0.99    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f12])).
% 3.79/0.99  
% 3.79/0.99  fof(f86,plain,(
% 3.79/0.99    v3_orders_2(sK8)),
% 3.79/0.99    inference(cnf_transformation,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  fof(f93,plain,(
% 3.79/0.99    k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != sK10),
% 3.79/0.99    inference(cnf_transformation,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  fof(f30,plain,(
% 3.79/0.99    ! [X0] : ((v2_lattice3(X0) <=> sP0(X0)) | ~sP1(X0))),
% 3.79/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.79/0.99  
% 3.79/0.99  fof(f32,plain,(
% 3.79/0.99    ! [X0] : (((v2_lattice3(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_lattice3(X0))) | ~sP1(X0))),
% 3.79/0.99    inference(nnf_transformation,[],[f30])).
% 3.79/0.99  
% 3.79/0.99  fof(f57,plain,(
% 3.79/0.99    ( ! [X0] : (sP0(X0) | ~v2_lattice3(X0) | ~sP1(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f32])).
% 3.79/0.99  
% 3.79/0.99  fof(f4,axiom,(
% 3.79/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f17,plain,(
% 3.79/0.99    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f4])).
% 3.79/0.99  
% 3.79/0.99  fof(f18,plain,(
% 3.79/0.99    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.79/0.99    inference(flattening,[],[f17])).
% 3.79/0.99  
% 3.79/0.99  fof(f31,plain,(
% 3.79/0.99    ! [X0] : (sP1(X0) | ~l1_orders_2(X0))),
% 3.79/0.99    inference(definition_folding,[],[f18,f30,f29])).
% 3.79/0.99  
% 3.79/0.99  fof(f69,plain,(
% 3.79/0.99    ( ! [X0] : (sP1(X0) | ~l1_orders_2(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f31])).
% 3.79/0.99  
% 3.79/0.99  fof(f92,plain,(
% 3.79/0.99    m1_subset_1(sK10,u1_struct_0(sK8))),
% 3.79/0.99    inference(cnf_transformation,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  fof(f91,plain,(
% 3.79/0.99    m1_subset_1(sK9,u1_struct_0(sK8))),
% 3.79/0.99    inference(cnf_transformation,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | r1_orders_2(X0,X1,sK5(X0,X3,X2))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ sP0(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2992,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0_52,X0_53,X1_53)
% 3.79/0.99      | ~ r1_orders_2(X0_52,X0_53,X2_53)
% 3.79/0.99      | r1_orders_2(X0_52,X0_53,sK5(X0_52,X2_53,X1_53))
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 3.79/0.99      | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
% 3.79/0.99      | ~ sP0(X0_52) ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_16915,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),X0_53)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK5(sK8,sK9,X0_53))
% 3.79/0.99      | ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK9)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | ~ sP0(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2992]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_16917,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK5(sK8,sK9,sK10))
% 3.79/0.99      | ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK9)
% 3.79/0.99      | ~ m1_subset_1(sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | ~ sP0(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_16915]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3002,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0_52,X0_53,X1_53)
% 3.79/0.99      | r1_orders_2(X0_52,X2_53,X3_53)
% 3.79/0.99      | X2_53 != X0_53
% 3.79/0.99      | X3_53 != X1_53 ),
% 3.79/0.99      theory(equality) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6375,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 3.79/0.99      | r1_orders_2(sK8,k11_lattice3(sK8,sK9,X2_53),sK10)
% 3.79/0.99      | k11_lattice3(sK8,sK9,X2_53) != X0_53
% 3.79/0.99      | sK10 != X1_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3002]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11451,plain,
% 3.79/0.99      ( r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),X1_53)
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,X0_53)
% 3.79/0.99      | sK10 != X1_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_6375]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11452,plain,
% 3.79/0.99      ( k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,X0_53)
% 3.79/0.99      | sK10 != X1_53
% 3.79/0.99      | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = iProver_top
% 3.79/0.99      | r1_orders_2(sK8,sK5(sK8,sK9,X0_53),X1_53) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_11451]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11454,plain,
% 3.79/0.99      ( k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,sK10)
% 3.79/0.99      | sK10 != sK10
% 3.79/0.99      | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = iProver_top
% 3.79/0.99      | r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_11452]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3003,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0_53,X0_54)
% 3.79/0.99      | m1_subset_1(X1_53,X0_54)
% 3.79/0.99      | X1_53 != X0_53 ),
% 3.79/0.99      theory(equality) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3924,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | X1_53 != X0_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3003]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4425,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) != X0_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3924]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11435,plain,
% 3.79/0.99      ( m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,X0_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4425]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11436,plain,
% 3.79/0.99      ( k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,X0_53)
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
% 3.79/0.99      | m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_11435]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11438,plain,
% 3.79/0.99      ( k11_lattice3(sK8,sK9,sK10) != sK5(sK8,sK9,sK10)
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
% 3.79/0.99      | m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_11436]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_14,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
% 3.79/0.99      | ~ sP0(X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2989,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 3.79/0.99      | m1_subset_1(sK5(X0_52,X1_53,X0_53),u1_struct_0(X0_52))
% 3.79/0.99      | ~ sP0(X0_52) ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9416,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | ~ sP0(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2989]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9417,plain,
% 3.79/0.99      ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8)) = iProver_top
% 3.79/0.99      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | sP0(sK8) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_9416]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9419,plain,
% 3.79/0.99      ( m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
% 3.79/0.99      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | sP0(sK8) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_9417]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9418,plain,
% 3.79/0.99      ( m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | ~ sP0(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_9416]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_12,plain,
% 3.79/0.99      ( r1_orders_2(X0,sK5(X0,X1,X2),X2)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ sP0(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2991,plain,
% 3.79/0.99      ( r1_orders_2(X0_52,sK5(X0_52,X0_53,X1_53),X1_53)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 3.79/0.99      | ~ sP0(X0_52) ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6851,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | ~ sP0(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2991]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6854,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10) = iProver_top
% 3.79/0.99      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | sP0(sK8) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_6851]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_23,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | v2_struct_0(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2,plain,
% 3.79/0.99      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_257,plain,
% 3.79/0.99      ( ~ v2_lattice3(X0)
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_23,c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_258,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_257]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_38,negated_conjecture,
% 3.79/0.99      ( v5_orders_2(sK8) ),
% 3.79/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_831,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1
% 3.79/0.99      | sK8 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_258,c_38]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_832,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X0)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ v2_lattice3(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8)
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_831]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_36,negated_conjecture,
% 3.79/0.99      ( v2_lattice3(sK8) ),
% 3.79/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_35,negated_conjecture,
% 3.79/0.99      ( l1_orders_2(sK8) ),
% 3.79/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_836,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X0)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_832,c_36,c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_837,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X0)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_836]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2976,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK7(sK8,X2_53,X1_53,X0_53),X0_53)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2_53,X1_53) = X0_53 ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_837]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4970,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,sK9)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,X0_53),X0_53)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = X0_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2976]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6692,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK5(sK8,sK9,X0_53))
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,X0_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4970]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6705,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK5(sK8,sK9,sK10))
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,sK10) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_6692]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_26,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | m1_subset_1(sK7(X0,X3,X2,X1),u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | v2_struct_0(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_238,plain,
% 3.79/0.99      ( ~ v2_lattice3(X0)
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | m1_subset_1(sK7(X0,X3,X2,X1),u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_26,c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_239,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | m1_subset_1(sK7(X0,X3,X2,X1),u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_238]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_926,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | m1_subset_1(sK7(X0,X3,X2,X1),u1_struct_0(X0))
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1
% 3.79/0.99      | sK8 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_239,c_38]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_927,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | m1_subset_1(sK7(sK8,X2,X1,X0),u1_struct_0(sK8))
% 3.79/0.99      | ~ v2_lattice3(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8)
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_926]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_931,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | m1_subset_1(sK7(sK8,X2,X1,X0),u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_927,c_36,c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_932,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | m1_subset_1(sK7(sK8,X2,X1,X0),u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_931]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2973,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 3.79/0.99      | m1_subset_1(sK7(sK8,X2_53,X1_53,X0_53),u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2_53,X1_53) = X0_53 ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_932]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4973,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,sK9)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | m1_subset_1(sK7(sK8,sK9,sK10,X0_53),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = X0_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2973]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6693,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
% 3.79/0.99      | m1_subset_1(sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,X0_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4973]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6701,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
% 3.79/0.99      | m1_subset_1(sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,sK10) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_6693]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_25,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | v2_struct_0(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_245,plain,
% 3.79/0.99      ( ~ v2_lattice3(X0)
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_25,c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_246,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_245]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_897,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1
% 3.79/0.99      | sK8 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_246,c_38]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_898,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X2)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ v2_lattice3(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8)
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_897]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_900,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X2)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_898,c_36,c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_901,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X2)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_900]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2974,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,X2_53,X1_53,X0_53),X2_53)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2_53,X1_53) = X0_53 ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_901]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4972,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,sK9)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,sK9,sK10,X0_53),sK9)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = X0_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2974]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6694,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK9)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,X0_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4972]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6697,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK9)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,sK10) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_6694]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_16,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v1_lattice3(X0)
% 3.79/0.99      | v2_struct_0(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k10_lattice3(X0,X1,X3) = X2 ),
% 3.79/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1,plain,
% 3.79/0.99      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_302,plain,
% 3.79/0.99      ( ~ v1_lattice3(X0)
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
% 3.79/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k10_lattice3(X0,X1,X3) = X2 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_16,c_1]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_303,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v1_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k10_lattice3(X0,X1,X3) = X2 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_302]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_37,negated_conjecture,
% 3.79/0.99      ( v1_lattice3(sK8) ),
% 3.79/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_551,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X3,X2))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k10_lattice3(X0,X1,X3) = X2
% 3.79/0.99      | sK8 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_303,c_37]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_552,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X2,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ v5_orders_2(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8)
% 3.79/0.99      | k10_lattice3(sK8,X2,X0) = X1 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_551]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_556,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X2,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k10_lattice3(sK8,X2,X0) = X1 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_552,c_38,c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_557,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X2,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | k10_lattice3(sK8,X2,X0) = X1 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_556]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2984,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 3.79/0.99      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 3.79/0.99      | ~ r1_orders_2(sK8,X1_53,sK6(sK8,X2_53,X0_53,X1_53))
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 3.79/0.99      | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_557]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6667,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK10,sK6(sK8,k11_lattice3(sK8,sK9,sK10),X0_53,sK10))
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = sK10 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2984]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6683,plain,
% 3.79/0.99      ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = sK10
% 3.79/0.99      | r1_orders_2(sK8,X0_53,sK10) != iProver_top
% 3.79/0.99      | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != iProver_top
% 3.79/0.99      | r1_orders_2(sK8,sK10,sK6(sK8,k11_lattice3(sK8,sK9,sK10),X0_53,sK10)) != iProver_top
% 3.79/0.99      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_6667]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6685,plain,
% 3.79/0.99      ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = sK10
% 3.79/0.99      | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != iProver_top
% 3.79/0.99      | r1_orders_2(sK8,sK10,sK6(sK8,k11_lattice3(sK8,sK9,sK10),sK10,sK10)) != iProver_top
% 3.79/0.99      | r1_orders_2(sK8,sK10,sK10) != iProver_top
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_6683]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_17,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.79/0.99      | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v1_lattice3(X0)
% 3.79/0.99      | v2_struct_0(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k10_lattice3(X0,X1,X3) = X2 ),
% 3.79/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_297,plain,
% 3.79/0.99      ( ~ v1_lattice3(X0)
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
% 3.79/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k10_lattice3(X0,X1,X3) = X2 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_17,c_1]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_298,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.79/0.99      | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v1_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k10_lattice3(X0,X1,X3) = X2 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_297]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_584,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.79/0.99      | r1_orders_2(X0,X3,sK6(X0,X1,X3,X2))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k10_lattice3(X0,X1,X3) = X2
% 3.79/0.99      | sK8 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_298,c_37]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_585,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X2,X1)
% 3.79/0.99      | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ v5_orders_2(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8)
% 3.79/0.99      | k10_lattice3(sK8,X2,X0) = X1 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_584]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_589,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X2,X1)
% 3.79/0.99      | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k10_lattice3(sK8,X2,X0) = X1 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_585,c_38,c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_590,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X2,X1)
% 3.79/0.99      | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | k10_lattice3(sK8,X2,X0) = X1 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_589]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2983,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 3.79/0.99      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 3.79/0.99      | r1_orders_2(sK8,X0_53,sK6(sK8,X2_53,X0_53,X1_53))
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 3.79/0.99      | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_590]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6668,plain,
% 3.79/0.99      ( r1_orders_2(sK8,X0_53,sK6(sK8,k11_lattice3(sK8,sK9,sK10),X0_53,sK10))
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = sK10 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2983]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6679,plain,
% 3.79/0.99      ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = sK10
% 3.79/0.99      | r1_orders_2(sK8,X0_53,sK6(sK8,k11_lattice3(sK8,sK9,sK10),X0_53,sK10)) = iProver_top
% 3.79/0.99      | r1_orders_2(sK8,X0_53,sK10) != iProver_top
% 3.79/0.99      | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != iProver_top
% 3.79/0.99      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_6668]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6681,plain,
% 3.79/0.99      ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = sK10
% 3.79/0.99      | r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != iProver_top
% 3.79/0.99      | r1_orders_2(sK8,sK10,sK6(sK8,k11_lattice3(sK8,sK9,sK10),sK10,sK10)) = iProver_top
% 3.79/0.99      | r1_orders_2(sK8,sK10,sK10) != iProver_top
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_6679]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3001,plain,
% 3.79/0.99      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 3.79/0.99      theory(equality) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4318,plain,
% 3.79/0.99      ( k10_lattice3(sK8,X0_53,X1_53) != X2_53
% 3.79/0.99      | sK10 != X2_53
% 3.79/0.99      | sK10 = k10_lattice3(sK8,X0_53,X1_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3001]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6050,plain,
% 3.79/0.99      ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) != X1_53
% 3.79/0.99      | sK10 != X1_53
% 3.79/0.99      | sK10 = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4318]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6051,plain,
% 3.79/0.99      ( k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != sK10
% 3.79/0.99      | sK10 = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | sK10 != sK10 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_6050]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_13,plain,
% 3.79/0.99      ( r1_orders_2(X0,sK5(X0,X1,X2),X1)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ sP0(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2990,plain,
% 3.79/0.99      ( r1_orders_2(X0_52,sK5(X0_52,X0_53,X1_53),X0_53)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 3.79/0.99      | ~ sP0(X0_52) ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5508,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | ~ sP0(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2990]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5514,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | ~ sP0(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_5508]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_24,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | v2_struct_0(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_252,plain,
% 3.79/0.99      ( ~ v2_lattice3(X0)
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_24,c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_253,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v5_orders_2(X0)
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_252]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_864,plain,
% 3.79/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.79/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.79/0.99      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.79/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.79/0.99      | ~ v2_lattice3(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | k11_lattice3(X0,X3,X2) = X1
% 3.79/0.99      | sK8 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_253,c_38]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_865,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X1)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ v2_lattice3(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8)
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_864]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_869,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X1)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_865,c_36,c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_870,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0,X1)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0,X2)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,X2,X1,X0),X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2,X1) = X0 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_869]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2975,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,X2_53,X1_53,X0_53),X1_53)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,X2_53,X1_53) = X0_53 ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_870]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4971,plain,
% 3.79/0.99      ( ~ r1_orders_2(sK8,X0_53,sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,X0_53,sK9)
% 3.79/0.99      | r1_orders_2(sK8,sK7(sK8,sK9,sK10,X0_53),sK10)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = X0_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2975]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5507,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,X0_53)),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,X0_53),sK9)
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,X0_53),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,X0_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4971]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5510,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK7(sK8,sK9,sK10,sK5(sK8,sK9,sK10)),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK10)
% 3.79/0.99      | ~ r1_orders_2(sK8,sK5(sK8,sK9,sK10),sK9)
% 3.79/0.99      | ~ m1_subset_1(sK5(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k11_lattice3(sK8,sK9,sK10) = sK5(sK8,sK9,sK10) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_5507]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4000,plain,
% 3.79/0.99      ( k13_lattice3(sK8,X0_53,X1_53) != X2_53
% 3.79/0.99      | sK10 != X2_53
% 3.79/0.99      | sK10 = k13_lattice3(sK8,X0_53,X1_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3001]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4203,plain,
% 3.79/0.99      ( k13_lattice3(sK8,X0_53,X1_53) != k10_lattice3(sK8,X0_53,X1_53)
% 3.79/0.99      | sK10 = k13_lattice3(sK8,X0_53,X1_53)
% 3.79/0.99      | sK10 != k10_lattice3(sK8,X0_53,X1_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4000]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5046,plain,
% 3.79/0.99      ( k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) != k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53)
% 3.79/0.99      | sK10 = k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53)
% 3.79/0.99      | sK10 != k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4203]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5047,plain,
% 3.79/0.99      ( k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) != k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | sK10 = k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | sK10 != k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_5046]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_31,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | ~ v5_orders_2(X1)
% 3.79/0.99      | ~ v1_lattice3(X1)
% 3.79/0.99      | ~ l1_orders_2(X1)
% 3.79/0.99      | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2) ),
% 3.79/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_756,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | ~ v5_orders_2(X1)
% 3.79/0.99      | ~ l1_orders_2(X1)
% 3.79/0.99      | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2)
% 3.79/0.99      | sK8 != X1 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_37]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_757,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ v5_orders_2(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8)
% 3.79/0.99      | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_756]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_761,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_757,c_38,c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_762,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k13_lattice3(sK8,X1,X0) = k10_lattice3(sK8,X1,X0) ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_761]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2977,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | k13_lattice3(sK8,X1_53,X0_53) = k10_lattice3(sK8,X1_53,X0_53) ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_762]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4992,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 3.79/0.99      | k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2977]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4997,plain,
% 3.79/0.99      ( k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53) = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53)
% 3.79/0.99      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_4992]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4999,plain,
% 3.79/0.99      ( k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) = k10_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | m1_subset_1(k11_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4997]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3906,plain,
% 3.79/0.99      ( X0_53 != X1_53
% 3.79/0.99      | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != X1_53
% 3.79/0.99      | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = X0_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3001]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4051,plain,
% 3.79/0.99      ( X0_53 != k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X1_53)
% 3.79/0.99      | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = X0_53
% 3.79/0.99      | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X1_53) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3906]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4052,plain,
% 3.79/0.99      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = sK10
% 3.79/0.99      | sK10 != k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4051]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_30,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | ~ v5_orders_2(X1)
% 3.79/0.99      | ~ v2_lattice3(X1)
% 3.79/0.99      | ~ l1_orders_2(X1)
% 3.79/0.99      | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2) ),
% 3.79/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1036,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | ~ v2_lattice3(X1)
% 3.79/0.99      | ~ l1_orders_2(X1)
% 3.79/0.99      | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2)
% 3.79/0.99      | sK8 != X1 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_38]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1037,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | ~ v2_lattice3(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8)
% 3.79/0.99      | k12_lattice3(sK8,X0,X1) = k11_lattice3(sK8,X0,X1) ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_1036]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1041,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k12_lattice3(sK8,X0,X1) = k11_lattice3(sK8,X0,X1) ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_1037,c_36,c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1042,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.79/0.99      | k12_lattice3(sK8,X1,X0) = k11_lattice3(sK8,X1,X0) ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_1041]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2969,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 3.79/0.99      | k12_lattice3(sK8,X1_53,X0_53) = k11_lattice3(sK8,X1_53,X0_53) ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_1042]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4003,plain,
% 3.79/0.99      ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 3.79/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.79/0.99      | k12_lattice3(sK8,sK9,sK10) = k11_lattice3(sK8,sK9,sK10) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2969]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3005,plain,
% 3.79/0.99      ( X0_53 != X1_53
% 3.79/0.99      | X2_53 != X3_53
% 3.79/0.99      | k13_lattice3(X0_52,X0_53,X2_53) = k13_lattice3(X0_52,X1_53,X3_53) ),
% 3.79/0.99      theory(equality) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3908,plain,
% 3.79/0.99      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = k13_lattice3(sK8,X0_53,X1_53)
% 3.79/0.99      | k12_lattice3(sK8,sK9,sK10) != X0_53
% 3.79/0.99      | sK10 != X1_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3005]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4002,plain,
% 3.79/0.99      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),X0_53)
% 3.79/0.99      | k12_lattice3(sK8,sK9,sK10) != k11_lattice3(sK8,sK9,sK10)
% 3.79/0.99      | sK10 != X0_53 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3908]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4004,plain,
% 3.79/0.99      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) = k13_lattice3(sK8,k11_lattice3(sK8,sK9,sK10),sK10)
% 3.79/0.99      | k12_lattice3(sK8,sK9,sK10) != k11_lattice3(sK8,sK9,sK10)
% 3.79/0.99      | sK10 != sK10 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4002]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_0,plain,
% 3.79/0.99      ( r1_orders_2(X0,X1,X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | v2_struct_0(X0)
% 3.79/0.99      | ~ v3_orders_2(X0)
% 3.79/0.99      | ~ l1_orders_2(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_39,negated_conjecture,
% 3.79/0.99      ( v3_orders_2(sK8) ),
% 3.79/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_496,plain,
% 3.79/0.99      ( r1_orders_2(X0,X1,X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.79/0.99      | v2_struct_0(X0)
% 3.79/0.99      | ~ l1_orders_2(X0)
% 3.79/0.99      | sK8 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_39]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_497,plain,
% 3.79/0.99      ( r1_orders_2(sK8,X0,X0)
% 3.79/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.79/0.99      | v2_struct_0(sK8)
% 3.79/0.99      | ~ l1_orders_2(sK8) ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_496]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_123,plain,
% 3.79/0.99      ( ~ v2_lattice3(sK8) | ~ v2_struct_0(sK8) | ~ l1_orders_2(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_501,plain,
% 3.79/0.99      ( r1_orders_2(sK8,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_497,c_36,c_35,c_123]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2985,plain,
% 3.79/0.99      ( r1_orders_2(sK8,X0_53,X0_53)
% 3.79/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK8)) ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_501]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3030,plain,
% 3.79/0.99      ( r1_orders_2(sK8,X0_53,X0_53) = iProver_top
% 3.79/0.99      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2985]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3032,plain,
% 3.79/0.99      ( r1_orders_2(sK8,sK10,sK10) = iProver_top
% 3.79/0.99      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3030]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_32,negated_conjecture,
% 3.79/0.99      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != sK10 ),
% 3.79/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2988,negated_conjecture,
% 3.79/0.99      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK10),sK10) != sK10 ),
% 3.79/0.99      inference(subtyping,[status(esa)],[c_32]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3000,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3011,plain,
% 3.79/0.99      ( sK10 = sK10 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3000]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4,plain,
% 3.79/0.99      ( ~ sP1(X0) | sP0(X0) | ~ v2_lattice3(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_118,plain,
% 3.79/0.99      ( sP1(X0) != iProver_top
% 3.79/0.99      | sP0(X0) = iProver_top
% 3.79/0.99      | v2_lattice3(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_120,plain,
% 3.79/0.99      ( sP1(sK8) != iProver_top
% 3.79/0.99      | sP0(sK8) = iProver_top
% 3.79/0.99      | v2_lattice3(sK8) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_118]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_119,plain,
% 3.79/0.99      ( ~ sP1(sK8) | sP0(sK8) | ~ v2_lattice3(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_15,plain,
% 3.79/0.99      ( sP1(X0) | ~ l1_orders_2(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_87,plain,
% 3.79/0.99      ( sP1(X0) = iProver_top | l1_orders_2(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_89,plain,
% 3.79/0.99      ( sP1(sK8) = iProver_top | l1_orders_2(sK8) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_87]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_88,plain,
% 3.79/0.99      ( sP1(sK8) | ~ l1_orders_2(sK8) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_33,negated_conjecture,
% 3.79/0.99      ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_46,plain,
% 3.79/0.99      ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_34,negated_conjecture,
% 3.79/0.99      ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_45,plain,
% 3.79/0.99      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_44,plain,
% 3.79/0.99      ( l1_orders_2(sK8) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_43,plain,
% 3.79/0.99      ( v2_lattice3(sK8) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(contradiction,plain,
% 3.79/0.99      ( $false ),
% 3.79/0.99      inference(minisat,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_16917,c_11454,c_11438,c_9419,c_9418,c_6854,c_6851,
% 3.79/0.99                 c_6705,c_6701,c_6697,c_6685,c_6681,c_6051,c_5514,c_5510,
% 3.79/0.99                 c_5047,c_4999,c_4052,c_4003,c_4004,c_3032,c_2988,c_3011,
% 3.79/0.99                 c_120,c_119,c_89,c_88,c_46,c_33,c_45,c_34,c_44,c_35,
% 3.79/0.99                 c_43,c_36]) ).
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  ------                               Statistics
% 3.79/0.99  
% 3.79/0.99  ------ General
% 3.79/0.99  
% 3.79/0.99  abstr_ref_over_cycles:                  0
% 3.79/0.99  abstr_ref_under_cycles:                 0
% 3.79/0.99  gc_basic_clause_elim:                   0
% 3.79/0.99  forced_gc_time:                         0
% 3.79/0.99  parsing_time:                           0.011
% 3.79/0.99  unif_index_cands_time:                  0.
% 3.79/0.99  unif_index_add_time:                    0.
% 3.79/0.99  orderings_time:                         0.
% 3.79/0.99  out_proof_time:                         0.015
% 3.79/0.99  total_time:                             0.494
% 3.79/0.99  num_of_symbols:                         55
% 3.79/0.99  num_of_terms:                           13699
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing
% 3.79/0.99  
% 3.79/0.99  num_of_splits:                          0
% 3.79/0.99  num_of_split_atoms:                     0
% 3.79/0.99  num_of_reused_defs:                     0
% 3.79/0.99  num_eq_ax_congr_red:                    69
% 3.79/0.99  num_of_sem_filtered_clauses:            1
% 3.79/0.99  num_of_subtypes:                        3
% 3.79/0.99  monotx_restored_types:                  0
% 3.79/0.99  sat_num_of_epr_types:                   0
% 3.79/0.99  sat_num_of_non_cyclic_types:            0
% 3.79/0.99  sat_guarded_non_collapsed_types:        1
% 3.79/0.99  num_pure_diseq_elim:                    0
% 3.79/0.99  simp_replaced_by:                       0
% 3.79/0.99  res_preprocessed:                       146
% 3.79/0.99  prep_upred:                             0
% 3.79/0.99  prep_unflattend:                        39
% 3.79/0.99  smt_new_axioms:                         0
% 3.79/0.99  pred_elim_cands:                        3
% 3.79/0.99  pred_elim:                              7
% 3.79/0.99  pred_elim_cl:                           9
% 3.79/0.99  pred_elim_cycles:                       9
% 3.79/0.99  merged_defs:                            0
% 3.79/0.99  merged_defs_ncl:                        0
% 3.79/0.99  bin_hyper_res:                          0
% 3.79/0.99  prep_cycles:                            4
% 3.79/0.99  pred_elim_time:                         0.042
% 3.79/0.99  splitting_time:                         0.
% 3.79/0.99  sem_filter_time:                        0.
% 3.79/0.99  monotx_time:                            0.
% 3.79/0.99  subtype_inf_time:                       0.001
% 3.79/0.99  
% 3.79/0.99  ------ Problem properties
% 3.79/0.99  
% 3.79/0.99  clauses:                                31
% 3.79/0.99  conjectures:                            3
% 3.79/0.99  epr:                                    1
% 3.79/0.99  horn:                                   20
% 3.79/0.99  ground:                                 4
% 3.79/0.99  unary:                                  4
% 3.79/0.99  binary:                                 3
% 3.79/0.99  lits:                                   141
% 3.79/0.99  lits_eq:                                11
% 3.79/0.99  fd_pure:                                0
% 3.79/0.99  fd_pseudo:                              0
% 3.79/0.99  fd_cond:                                0
% 3.79/0.99  fd_pseudo_cond:                         8
% 3.79/0.99  ac_symbols:                             0
% 3.79/0.99  
% 3.79/0.99  ------ Propositional Solver
% 3.79/0.99  
% 3.79/0.99  prop_solver_calls:                      33
% 3.79/0.99  prop_fast_solver_calls:                 2513
% 3.79/0.99  smt_solver_calls:                       0
% 3.79/0.99  smt_fast_solver_calls:                  0
% 3.79/0.99  prop_num_of_clauses:                    4375
% 3.79/0.99  prop_preprocess_simplified:             12259
% 3.79/0.99  prop_fo_subsumed:                       69
% 3.79/0.99  prop_solver_time:                       0.
% 3.79/0.99  smt_solver_time:                        0.
% 3.79/0.99  smt_fast_solver_time:                   0.
% 3.79/0.99  prop_fast_solver_time:                  0.
% 3.79/0.99  prop_unsat_core_time:                   0.001
% 3.79/0.99  
% 3.79/0.99  ------ QBF
% 3.79/0.99  
% 3.79/0.99  qbf_q_res:                              0
% 3.79/0.99  qbf_num_tautologies:                    0
% 3.79/0.99  qbf_prep_cycles:                        0
% 3.79/0.99  
% 3.79/0.99  ------ BMC1
% 3.79/0.99  
% 3.79/0.99  bmc1_current_bound:                     -1
% 3.79/0.99  bmc1_last_solved_bound:                 -1
% 3.79/0.99  bmc1_unsat_core_size:                   -1
% 3.79/0.99  bmc1_unsat_core_parents_size:           -1
% 3.79/0.99  bmc1_merge_next_fun:                    0
% 3.79/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation
% 3.79/0.99  
% 3.79/0.99  inst_num_of_clauses:                    1329
% 3.79/0.99  inst_num_in_passive:                    191
% 3.79/0.99  inst_num_in_active:                     752
% 3.79/0.99  inst_num_in_unprocessed:                386
% 3.79/0.99  inst_num_of_loops:                      817
% 3.79/0.99  inst_num_of_learning_restarts:          0
% 3.79/0.99  inst_num_moves_active_passive:          57
% 3.79/0.99  inst_lit_activity:                      0
% 3.79/0.99  inst_lit_activity_moves:                0
% 3.79/0.99  inst_num_tautologies:                   0
% 3.79/0.99  inst_num_prop_implied:                  0
% 3.79/0.99  inst_num_existing_simplified:           0
% 3.79/0.99  inst_num_eq_res_simplified:             0
% 3.79/0.99  inst_num_child_elim:                    0
% 3.79/0.99  inst_num_of_dismatching_blockings:      685
% 3.79/0.99  inst_num_of_non_proper_insts:           2699
% 3.79/0.99  inst_num_of_duplicates:                 0
% 3.79/0.99  inst_inst_num_from_inst_to_res:         0
% 3.79/0.99  inst_dismatching_checking_time:         0.
% 3.79/0.99  
% 3.79/0.99  ------ Resolution
% 3.79/0.99  
% 3.79/0.99  res_num_of_clauses:                     0
% 3.79/0.99  res_num_in_passive:                     0
% 3.79/0.99  res_num_in_active:                      0
% 3.79/0.99  res_num_of_loops:                       150
% 3.79/0.99  res_forward_subset_subsumed:            182
% 3.79/0.99  res_backward_subset_subsumed:           0
% 3.79/0.99  res_forward_subsumed:                   0
% 3.79/0.99  res_backward_subsumed:                  0
% 3.79/0.99  res_forward_subsumption_resolution:     0
% 3.79/0.99  res_backward_subsumption_resolution:    0
% 3.79/0.99  res_clause_to_clause_subsumption:       3310
% 3.79/0.99  res_orphan_elimination:                 0
% 3.79/0.99  res_tautology_del:                      263
% 3.79/0.99  res_num_eq_res_simplified:              0
% 3.79/0.99  res_num_sel_changes:                    0
% 3.79/0.99  res_moves_from_active_to_pass:          0
% 3.79/0.99  
% 3.79/0.99  ------ Superposition
% 3.79/0.99  
% 3.79/0.99  sup_time_total:                         0.
% 3.79/0.99  sup_time_generating:                    0.
% 3.79/0.99  sup_time_sim_full:                      0.
% 3.79/0.99  sup_time_sim_immed:                     0.
% 3.79/0.99  
% 3.79/0.99  sup_num_of_clauses:                     338
% 3.79/0.99  sup_num_in_active:                      157
% 3.79/0.99  sup_num_in_passive:                     181
% 3.79/0.99  sup_num_of_loops:                       162
% 3.79/0.99  sup_fw_superposition:                   428
% 3.79/0.99  sup_bw_superposition:                   64
% 3.79/0.99  sup_immediate_simplified:               175
% 3.79/0.99  sup_given_eliminated:                   0
% 3.79/0.99  comparisons_done:                       0
% 3.79/0.99  comparisons_avoided:                    0
% 3.79/0.99  
% 3.79/0.99  ------ Simplifications
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  sim_fw_subset_subsumed:                 167
% 3.79/0.99  sim_bw_subset_subsumed:                 0
% 3.79/0.99  sim_fw_subsumed:                        4
% 3.79/0.99  sim_bw_subsumed:                        0
% 3.79/0.99  sim_fw_subsumption_res:                 2
% 3.79/0.99  sim_bw_subsumption_res:                 0
% 3.79/0.99  sim_tautology_del:                      5
% 3.79/0.99  sim_eq_tautology_del:                   0
% 3.79/0.99  sim_eq_res_simp:                        0
% 3.79/0.99  sim_fw_demodulated:                     0
% 3.79/0.99  sim_bw_demodulated:                     5
% 3.79/0.99  sim_light_normalised:                   8
% 3.79/0.99  sim_joinable_taut:                      0
% 3.79/0.99  sim_joinable_simp:                      0
% 3.79/0.99  sim_ac_normalised:                      0
% 3.79/0.99  sim_smt_subsumption:                    0
% 3.79/0.99  
%------------------------------------------------------------------------------
