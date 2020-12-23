%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1660+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:07 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  217 (1329 expanded)
%              Number of clauses        :  141 ( 341 expanded)
%              Number of leaves         :   21 ( 392 expanded)
%              Depth                    :   30
%              Number of atoms          : 1419 (15067 expanded)
%              Number of equality atoms :  308 ( 657 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   34 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
        & r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
        & r2_hidden(sK6(X0,X1,X5,X6),X1)
        & m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              | ~ r1_orders_2(X0,X2,X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,sK5(X0,X1),X4)
            | ~ r1_orders_2(X0,X2,X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                | ~ r1_orders_2(X0,sK4(X0,X1),X4)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,sK5(X0,X1),X4)
              | ~ r1_orders_2(X0,sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
                  & r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
                  & r2_hidden(sK6(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f28,f31,f30,f29])).

fof(f55,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK6(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
                        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k13_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
           => ( v1_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( ( r2_hidden(X3,X1)
                          & r2_hidden(X2,X1) )
                       => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k13_lattice3(X0,X2,sK11),X1)
        & r2_hidden(sK11,X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK11,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k13_lattice3(X0,sK10,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK10,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k13_lattice3(X0,X2,X3),sK9)
                  & r2_hidden(X3,sK9)
                  & r2_hidden(X2,sK9)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_waybel_0(sK9,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k13_lattice3(X0,X4,X5),sK9)
                  | ~ r2_hidden(X5,sK9)
                  | ~ r2_hidden(X4,sK9)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v1_waybel_0(sK9,X0) )
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v1_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(sK8,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(sK8)) )
                & m1_subset_1(X2,u1_struct_0(sK8)) )
            | ~ v1_waybel_0(X1,sK8) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k13_lattice3(sK8,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(sK8)) )
                | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
            | v1_waybel_0(X1,sK8) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
          & v12_waybel_0(X1,sK8) )
      & l1_orders_2(sK8)
      & v1_lattice3(sK8)
      & v5_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ( ~ r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9)
        & r2_hidden(sK11,sK9)
        & r2_hidden(sK10,sK9)
        & m1_subset_1(sK11,u1_struct_0(sK8))
        & m1_subset_1(sK10,u1_struct_0(sK8)) )
      | ~ v1_waybel_0(sK9,sK8) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(k13_lattice3(sK8,X4,X5),sK9)
              | ~ r2_hidden(X5,sK9)
              | ~ r2_hidden(X4,sK9)
              | ~ m1_subset_1(X5,u1_struct_0(sK8)) )
          | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
      | v1_waybel_0(sK9,sK8) )
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v12_waybel_0(sK9,sK8)
    & l1_orders_2(sK8)
    & v1_lattice3(sK8)
    & v5_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f40,f44,f43,f42,f41])).

fof(f76,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,X2)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK3(X0,X1),X2)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK3(X0,X1),sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f23,f22])).

fof(f46,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ( v1_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v1_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v1_waybel_0(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f10,f18,f17])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    ! [X4,X5] :
      ( r2_hidden(k13_lattice3(sK8,X4,X5),sK9)
      | ~ r2_hidden(X5,sK9)
      | ~ r2_hidden(X4,sK9)
      | ~ m1_subset_1(X5,u1_struct_0(sK8))
      | ~ m1_subset_1(X4,u1_struct_0(sK8))
      | v1_waybel_0(sK9,sK8) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_orders_2(X0,sK5(X0,X1),X4)
      | ~ r1_orders_2(X0,sK4(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,
    ( ~ r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9)
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,
    ( r2_hidden(sK11,sK9)
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,
    ( r2_hidden(sK10,sK9)
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,
    ( m1_subset_1(sK11,u1_struct_0(sK8))
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(sK6(X0,X1,X2,X3),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_349,plain,
    ( ~ sP0(X0_51,X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ r2_hidden(X1_52,X0_52)
    | ~ r2_hidden(X2_52,X0_52)
    | r2_hidden(sK6(X0_51,X0_52,X2_52,X1_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_999,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(X2_52,X0_52) != iProver_top
    | r2_hidden(X1_52,X0_52) != iProver_top
    | r2_hidden(sK6(X0_51,X0_52,X1_52,X2_52),X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X3,X1))
    | ~ sP0(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_351,plain,
    ( r1_orders_2(X0_51,X0_52,sK6(X0_51,X1_52,X2_52,X0_52))
    | ~ sP0(X0_51,X1_52)
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ r2_hidden(X2_52,X1_52)
    | ~ r2_hidden(X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_997,plain,
    ( r1_orders_2(X0_51,X0_52,sK6(X0_51,X1_52,X2_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(X2_52,X1_52) != iProver_top
    | r2_hidden(X0_52,X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_14,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X1,X3))
    | ~ sP0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_350,plain,
    ( r1_orders_2(X0_51,X0_52,sK6(X0_51,X1_52,X0_52,X2_52))
    | ~ sP0(X0_51,X1_52)
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ r2_hidden(X2_52,X1_52)
    | ~ r2_hidden(X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_998,plain,
    ( r1_orders_2(X0_51,X0_52,sK6(X0_51,X1_52,X0_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(X2_52,X1_52) != iProver_top
    | r2_hidden(X0_52,X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_23,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_341,plain,
    ( ~ r1_orders_2(X0_51,X0_52,X1_52)
    | ~ r1_orders_2(X0_51,X2_52,X1_52)
    | r1_orders_2(X0_51,k13_lattice3(X0_51,X2_52,X0_52),X1_52)
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(k13_lattice3(X0_51,X2_52,X0_52),u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ v1_lattice3(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1007,plain,
    ( r1_orders_2(X0_51,X0_52,X1_52) != iProver_top
    | r1_orders_2(X0_51,X2_52,X1_52) != iProver_top
    | r1_orders_2(X0_51,k13_lattice3(X0_51,X2_52,X0_52),X1_52) = iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(k13_lattice3(X0_51,X2_52,X0_52),u1_struct_0(X0_51)) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | m1_subset_1(k13_lattice3(X0_51,X0_52,X1_52),u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ v1_lattice3(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1002,plain,
    ( m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(k13_lattice3(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1341,plain,
    ( r1_orders_2(X0_51,X0_52,X1_52) != iProver_top
    | r1_orders_2(X0_51,X2_52,X1_52) != iProver_top
    | r1_orders_2(X0_51,k13_lattice3(X0_51,X2_52,X0_52),X1_52) = iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1007,c_1002])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_332,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1016,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_359,plain,
    ( ~ r1_orders_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ r2_hidden(X1_52,X2_52)
    | r2_hidden(X0_52,X2_52)
    | ~ v12_waybel_0(X2_52,X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_989,plain,
    ( r1_orders_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(X1_52,X2_52) != iProver_top
    | r2_hidden(X0_52,X2_52) = iProver_top
    | v12_waybel_0(X2_52,X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_2762,plain,
    ( r1_orders_2(sK8,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1_52,sK9) != iProver_top
    | r2_hidden(X0_52,sK9) = iProver_top
    | v12_waybel_0(sK9,sK8) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_989])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( v12_waybel_0(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3220,plain,
    ( r1_orders_2(sK8,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1_52,sK9) != iProver_top
    | r2_hidden(X0_52,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2762,c_39,c_40])).

cnf(c_3231,plain,
    ( r1_orders_2(sK8,k13_lattice3(sK8,X0_52,X1_52),X2_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X2_52,sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X0_52,X1_52),sK9) = iProver_top
    | v5_orders_2(sK8) != iProver_top
    | v1_lattice3(sK8) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_3220])).

cnf(c_36,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v5_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( v1_lattice3(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3374,plain,
    ( r2_hidden(k13_lattice3(sK8,X0_52,X1_52),sK9) = iProver_top
    | r2_hidden(X2_52,sK9) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,k13_lattice3(sK8,X0_52,X1_52),X2_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3231,c_37,c_38,c_39])).

cnf(c_3375,plain,
    ( r1_orders_2(sK8,k13_lattice3(sK8,X0_52,X1_52),X2_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X2_52,sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X0_52,X1_52),sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_3374])).

cnf(c_6105,plain,
    ( r1_orders_2(sK8,X0_52,X1_52) != iProver_top
    | r1_orders_2(sK8,X2_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1_52,sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9) = iProver_top
    | v5_orders_2(sK8) != iProver_top
    | v1_lattice3(sK8) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_3375])).

cnf(c_6696,plain,
    ( r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9) = iProver_top
    | r2_hidden(X1_52,sK9) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,X2_52,X1_52) != iProver_top
    | r1_orders_2(sK8,X0_52,X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6105,c_37,c_38,c_39])).

cnf(c_6697,plain,
    ( r1_orders_2(sK8,X0_52,X1_52) != iProver_top
    | r1_orders_2(sK8,X2_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1_52,sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_6696])).

cnf(c_6712,plain,
    ( r1_orders_2(sK8,X0_52,sK6(sK8,X1_52,X2_52,X3_52)) != iProver_top
    | sP0(sK8,X1_52) != iProver_top
    | m1_subset_1(X3_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X1_52,X2_52,X3_52),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X3_52,X1_52) != iProver_top
    | r2_hidden(X2_52,X1_52) != iProver_top
    | r2_hidden(sK6(sK8,X1_52,X2_52,X3_52),sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X0_52,X2_52),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_6697])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_348,plain,
    ( ~ sP0(X0_51,X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | m1_subset_1(sK6(X0_51,X0_52,X2_52,X1_52),u1_struct_0(X0_51))
    | ~ r2_hidden(X1_52,X0_52)
    | ~ r2_hidden(X2_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1000,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(sK6(X0_51,X0_52,X1_52,X2_52),u1_struct_0(X0_51)) = iProver_top
    | r2_hidden(X2_52,X0_52) != iProver_top
    | r2_hidden(X1_52,X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_10427,plain,
    ( r1_orders_2(sK8,X0_52,sK6(sK8,X1_52,X2_52,X3_52)) != iProver_top
    | sP0(sK8,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X3_52,X1_52) != iProver_top
    | r2_hidden(X2_52,X1_52) != iProver_top
    | r2_hidden(sK6(sK8,X1_52,X2_52,X3_52),sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X0_52,X2_52),sK9) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6712,c_1000])).

cnf(c_10433,plain,
    ( sP0(sK8,X0_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1_52,X0_52) != iProver_top
    | r2_hidden(X2_52,X0_52) != iProver_top
    | r2_hidden(sK6(sK8,X0_52,X1_52,X2_52),sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X2_52,X1_52),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_10427])).

cnf(c_14025,plain,
    ( sP0(sK8,sK9) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0_52,sK9) != iProver_top
    | r2_hidden(X1_52,sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X1_52,X0_52),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_10433])).

cnf(c_41,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v1_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_357,plain,
    ( ~ sP1(X0_52,X0_51)
    | sP0(X0_51,X0_52)
    | ~ v1_waybel_0(X0_52,X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_391,plain,
    ( sP1(X0_52,X0_51) != iProver_top
    | sP0(X0_51,X0_52) = iProver_top
    | v1_waybel_0(X0_52,X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_393,plain,
    ( sP1(sK9,sK8) != iProver_top
    | sP0(sK8,sK9) = iProver_top
    | v1_waybel_0(sK9,sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_17,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_347,plain,
    ( sP1(X0_52,X0_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_419,plain,
    ( sP1(X0_52,X0_51) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_421,plain,
    ( sP1(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_367,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_366,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1771,plain,
    ( X0_52 != X1_52
    | X1_52 = X0_52 ),
    inference(resolution,[status(thm)],[c_367,c_366])).

cnf(c_373,plain,
    ( X0_52 != X1_52
    | X2_52 != X3_52
    | k13_lattice3(X0_51,X0_52,X2_52) = k13_lattice3(X0_51,X1_52,X3_52) ),
    theory(equality)).

cnf(c_2375,plain,
    ( X0_52 != X1_52
    | X2_52 != X3_52
    | k13_lattice3(X0_51,X1_52,X3_52) = k13_lattice3(X0_51,X0_52,X2_52) ),
    inference(resolution,[status(thm)],[c_1771,c_373])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | r2_hidden(X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_1957,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | r2_hidden(X2_52,X1_52)
    | X2_52 != X0_52 ),
    inference(resolution,[status(thm)],[c_369,c_366])).

cnf(c_2427,plain,
    ( ~ r2_hidden(k13_lattice3(X0_51,X0_52,X1_52),X2_52)
    | r2_hidden(k13_lattice3(X0_51,X3_52,X4_52),X2_52)
    | X0_52 != X3_52
    | X1_52 != X4_52 ),
    inference(resolution,[status(thm)],[c_2375,c_1957])).

cnf(c_31,negated_conjecture,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X0,sK9)
    | ~ r2_hidden(X1,sK9)
    | r2_hidden(k13_lattice3(sK8,X1,X0),sK9) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_333,negated_conjecture,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X1_52,X0_52),sK9) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2774,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X2_52,X3_52),sK9)
    | X1_52 != X2_52
    | X0_52 != X3_52 ),
    inference(resolution,[status(thm)],[c_2427,c_333])).

cnf(c_2796,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(X0_51,X1_52,X2_52),u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(k13_lattice3(X0_51,X1_52,X2_52),sK9)
    | r2_hidden(k13_lattice3(sK8,X3_52,k13_lattice3(X0_51,X4_52,X5_52)),sK9)
    | X0_52 != X3_52
    | X1_52 != X4_52
    | X2_52 != X5_52 ),
    inference(resolution,[status(thm)],[c_2774,c_373])).

cnf(c_3605,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(k13_lattice3(sK8,X1_52,X2_52),sK9)
    | r2_hidden(k13_lattice3(sK8,X3_52,k13_lattice3(sK8,X4_52,X5_52)),sK9)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | X0_52 != X3_52
    | X1_52 != X4_52
    | X2_52 != X5_52 ),
    inference(resolution,[status(thm)],[c_2796,c_346])).

cnf(c_7129,plain,
    ( r2_hidden(k13_lattice3(sK8,X3_52,k13_lattice3(sK8,X4_52,X5_52)),sK9)
    | ~ r2_hidden(k13_lattice3(sK8,X1_52,X2_52),sK9)
    | ~ r2_hidden(X0_52,sK9)
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | v1_waybel_0(sK9,sK8)
    | X0_52 != X3_52
    | X1_52 != X4_52
    | X2_52 != X5_52 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3605,c_36,c_35,c_34])).

cnf(c_7130,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(k13_lattice3(sK8,X1_52,X2_52),sK9)
    | r2_hidden(k13_lattice3(sK8,X3_52,k13_lattice3(sK8,X4_52,X5_52)),sK9)
    | X0_52 != X3_52
    | X1_52 != X4_52
    | X2_52 != X5_52 ),
    inference(renaming,[status(thm)],[c_7129])).

cnf(c_7177,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(X1_52,sK9)
    | ~ r2_hidden(X2_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X3_52,k13_lattice3(sK8,X4_52,X5_52)),sK9)
    | X0_52 != X3_52
    | X1_52 != X4_52
    | X2_52 != X5_52 ),
    inference(resolution,[status(thm)],[c_7130,c_333])).

cnf(c_7203,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(X1_52,sK9)
    | ~ r2_hidden(X2_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X3_52,k13_lattice3(sK8,X4_52,X2_52)),sK9)
    | X0_52 != X3_52
    | X1_52 != X4_52 ),
    inference(resolution,[status(thm)],[c_7177,c_366])).

cnf(c_7269,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(X1_52,sK9)
    | ~ r2_hidden(X2_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X3_52,k13_lattice3(sK8,X1_52,X2_52)),sK9)
    | X0_52 != X3_52 ),
    inference(resolution,[status(thm)],[c_7203,c_366])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v1_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_358,plain,
    ( ~ sP1(X0_52,X0_51)
    | ~ sP0(X0_51,X0_52)
    | v1_waybel_0(X0_52,X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_389,plain,
    ( ~ sP1(sK9,sK8)
    | ~ sP0(sK8,sK9)
    | v1_waybel_0(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_9,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_355,plain,
    ( sP0(X0_51,X0_52)
    | r2_hidden(sK5(X0_51,X0_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_398,plain,
    ( sP0(sK8,sK9)
    | r2_hidden(sK5(sK8,sK9),sK9) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_10,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK4(X0,X1),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_354,plain,
    ( sP0(X0_51,X0_52)
    | r2_hidden(sK4(X0_51,X0_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_401,plain,
    ( sP0(sK8,sK9)
    | r2_hidden(sK4(sK8,sK9),sK9) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_11,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_353,plain,
    ( sP0(X0_51,X0_52)
    | m1_subset_1(sK5(X0_51,X0_52),u1_struct_0(X0_51)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_404,plain,
    ( sP0(sK8,sK9)
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_12,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_352,plain,
    ( sP0(X0_51,X0_52)
    | m1_subset_1(sK4(X0_51,X0_52),u1_struct_0(X0_51)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_407,plain,
    ( sP0(sK8,sK9)
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_420,plain,
    ( sP1(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_2245,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | m1_subset_1(k13_lattice3(X0_51,X0_52,sK4(X0_51,X1_52)),u1_struct_0(X0_51))
    | ~ m1_subset_1(sK4(X0_51,X1_52),u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ v1_lattice3(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_2703,plain,
    ( m1_subset_1(k13_lattice3(X0_51,sK5(X0_51,X0_52),sK4(X0_51,X1_52)),u1_struct_0(X0_51))
    | ~ m1_subset_1(sK4(X0_51,X1_52),u1_struct_0(X0_51))
    | ~ m1_subset_1(sK5(X0_51,X0_52),u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ v1_lattice3(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_2705,plain,
    ( m1_subset_1(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_2703])).

cnf(c_2324,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(X0_51,sK9),u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | r2_hidden(k13_lattice3(sK8,sK5(X0_51,sK9),X0_52),sK9)
    | ~ r2_hidden(sK5(X0_51,sK9),sK9) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_2837,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,X0_52),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(X0_51,sK9),u1_struct_0(sK8))
    | r2_hidden(k13_lattice3(sK8,sK5(X0_51,sK9),sK4(sK8,X0_52)),sK9)
    | ~ r2_hidden(sK4(sK8,X0_52),sK9)
    | ~ r2_hidden(sK5(X0_51,sK9),sK9) ),
    inference(instantiation,[status(thm)],[c_2324])).

cnf(c_2839,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | r2_hidden(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),sK9)
    | ~ r2_hidden(sK4(sK8,sK9),sK9)
    | ~ r2_hidden(sK5(sK8,sK9),sK9) ),
    inference(instantiation,[status(thm)],[c_2837])).

cnf(c_25,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_339,plain,
    ( r1_orders_2(X0_51,X0_52,k13_lattice3(X0_51,X0_52,X1_52))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(k13_lattice3(X0_51,X0_52,X1_52),u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ v1_lattice3(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1009,plain,
    ( r1_orders_2(X0_51,X0_52,k13_lattice3(X0_51,X0_52,X1_52)) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(k13_lattice3(X0_51,X0_52,X1_52),u1_struct_0(X0_51)) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_1228,plain,
    ( r1_orders_2(X0_51,X0_52,k13_lattice3(X0_51,X0_52,X1_52)) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1009,c_1002])).

cnf(c_24,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_340,plain,
    ( r1_orders_2(X0_51,X0_52,k13_lattice3(X0_51,X1_52,X0_52))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(k13_lattice3(X0_51,X1_52,X0_52),u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ v1_lattice3(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1008,plain,
    ( r1_orders_2(X0_51,X0_52,k13_lattice3(X0_51,X1_52,X0_52)) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(k13_lattice3(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_1214,plain,
    ( r1_orders_2(X0_51,X0_52,k13_lattice3(X0_51,X1_52,X0_52)) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1008,c_1002])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,sK4(X0,X1),X2)
    | ~ r1_orders_2(X0,sK5(X0,X1),X2)
    | sP0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_356,plain,
    ( ~ r1_orders_2(X0_51,sK4(X0_51,X0_52),X1_52)
    | ~ r1_orders_2(X0_51,sK5(X0_51,X0_52),X1_52)
    | sP0(X0_51,X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ r2_hidden(X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_992,plain,
    ( r1_orders_2(X0_51,sK4(X0_51,X0_52),X1_52) != iProver_top
    | r1_orders_2(X0_51,sK5(X0_51,X0_52),X1_52) != iProver_top
    | sP0(X0_51,X0_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(X1_52,X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_2465,plain,
    ( r1_orders_2(X0_51,sK5(X0_51,X0_52),k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52))) != iProver_top
    | sP0(X0_51,X0_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52)),u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(sK4(X0_51,X0_52),u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52)),X0_52) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_992])).

cnf(c_406,plain,
    ( sP0(X0_51,X0_52) = iProver_top
    | m1_subset_1(sK4(X0_51,X0_52),u1_struct_0(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_7350,plain,
    ( m1_subset_1(k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52)),u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | sP0(X0_51,X0_52) = iProver_top
    | r1_orders_2(X0_51,sK5(X0_51,X0_52),k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52))) != iProver_top
    | r2_hidden(k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52)),X0_52) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2465,c_406])).

cnf(c_7351,plain,
    ( r1_orders_2(X0_51,sK5(X0_51,X0_52),k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52))) != iProver_top
    | sP0(X0_51,X0_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52)),u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(k13_lattice3(X0_51,X1_52,sK4(X0_51,X0_52)),X0_52) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_7350])).

cnf(c_7364,plain,
    ( sP0(X0_51,X0_52) = iProver_top
    | m1_subset_1(k13_lattice3(X0_51,sK5(X0_51,X0_52),sK4(X0_51,X0_52)),u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(sK4(X0_51,X0_52),u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(sK5(X0_51,X0_52),u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(k13_lattice3(X0_51,sK5(X0_51,X0_52),sK4(X0_51,X0_52)),X0_52) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | v1_lattice3(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_7351])).

cnf(c_7365,plain,
    ( sP0(X0_51,X0_52)
    | ~ m1_subset_1(k13_lattice3(X0_51,sK5(X0_51,X0_52),sK4(X0_51,X0_52)),u1_struct_0(X0_51))
    | ~ m1_subset_1(sK4(X0_51,X0_52),u1_struct_0(X0_51))
    | ~ m1_subset_1(sK5(X0_51,X0_52),u1_struct_0(X0_51))
    | ~ r2_hidden(k13_lattice3(X0_51,sK5(X0_51,X0_52),sK4(X0_51,X0_52)),X0_52)
    | ~ v5_orders_2(X0_51)
    | ~ v1_lattice3(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7364])).

cnf(c_7367,plain,
    ( sP0(sK8,sK9)
    | ~ m1_subset_1(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_hidden(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),sK9)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_7365])).

cnf(c_7369,plain,
    ( v1_waybel_0(sK9,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7269,c_36,c_35,c_34,c_32,c_389,c_398,c_401,c_404,c_407,c_420,c_2705,c_2839,c_7367])).

cnf(c_7371,plain,
    ( v1_waybel_0(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7369])).

cnf(c_3000,plain,
    ( ~ r1_orders_2(X0_51,X0_52,X1_52)
    | ~ r1_orders_2(X0_51,X2_52,X1_52)
    | r1_orders_2(X0_51,k13_lattice3(X0_51,X2_52,X0_52),X1_52)
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ v1_lattice3(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_346,c_341])).

cnf(c_7528,plain,
    ( ~ r1_orders_2(sK8,X0_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(X0_52,sK9)
    | ~ v12_waybel_0(sK9,sK8)
    | ~ l1_orders_2(sK8) ),
    inference(resolution,[status(thm)],[c_359,c_332])).

cnf(c_3222,plain,
    ( ~ r1_orders_2(sK8,X0_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(X0_52,sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3220])).

cnf(c_7582,plain,
    ( ~ r1_orders_2(sK8,X0_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(X0_52,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7528,c_3222])).

cnf(c_10015,plain,
    ( ~ r1_orders_2(sK8,X0_52,X1_52)
    | ~ r1_orders_2(sK8,X2_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X2_52,X0_52),u1_struct_0(sK8))
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(resolution,[status(thm)],[c_3000,c_7582])).

cnf(c_6698,plain,
    ( ~ r1_orders_2(sK8,X0_52,X1_52)
    | ~ r1_orders_2(sK8,X2_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6697])).

cnf(c_10111,plain,
    ( r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9)
    | ~ r2_hidden(X1_52,sK9)
    | ~ r1_orders_2(sK8,X0_52,X1_52)
    | ~ r1_orders_2(sK8,X2_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10015,c_6698])).

cnf(c_10112,plain,
    ( ~ r1_orders_2(sK8,X0_52,X1_52)
    | ~ r1_orders_2(sK8,X2_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9) ),
    inference(renaming,[status(thm)],[c_10111])).

cnf(c_10159,plain,
    ( ~ r1_orders_2(sK8,X0_52,sK6(sK8,X1_52,X2_52,X3_52))
    | ~ sP0(sK8,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_52,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_52,X2_52,X3_52),u1_struct_0(sK8))
    | ~ r2_hidden(X3_52,X1_52)
    | ~ r2_hidden(X2_52,X1_52)
    | ~ r2_hidden(sK6(sK8,X1_52,X2_52,X3_52),sK9)
    | r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9) ),
    inference(resolution,[status(thm)],[c_10112,c_350])).

cnf(c_10549,plain,
    ( ~ r1_orders_2(sK8,X0_52,sK6(sK8,X1_52,X2_52,X3_52))
    | ~ sP0(sK8,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_52,u1_struct_0(sK8))
    | ~ r2_hidden(X3_52,X1_52)
    | ~ r2_hidden(X2_52,X1_52)
    | ~ r2_hidden(sK6(sK8,X1_52,X2_52,X3_52),sK9)
    | r2_hidden(k13_lattice3(sK8,X2_52,X0_52),sK9) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10159,c_348])).

cnf(c_11747,plain,
    ( ~ sP0(sK8,X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK8))
    | ~ r2_hidden(X2_52,X0_52)
    | ~ r2_hidden(X1_52,X0_52)
    | ~ r2_hidden(sK6(sK8,X0_52,X2_52,X1_52),sK9)
    | r2_hidden(k13_lattice3(sK8,X2_52,X1_52),sK9) ),
    inference(resolution,[status(thm)],[c_10549,c_351])).

cnf(c_13704,plain,
    ( ~ sP0(sK8,sK9)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK8))
    | ~ r2_hidden(X0_52,sK9)
    | ~ r2_hidden(X1_52,sK9)
    | r2_hidden(k13_lattice3(sK8,X1_52,X0_52),sK9) ),
    inference(resolution,[status(thm)],[c_11747,c_349])).

cnf(c_13705,plain,
    ( sP0(sK8,sK9) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0_52,sK9) != iProver_top
    | r2_hidden(X1_52,sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X1_52,X0_52),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13704])).

cnf(c_14028,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0_52,sK9) != iProver_top
    | r2_hidden(X1_52,sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X1_52,X0_52),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14025,c_39,c_41,c_393,c_421,c_7371,c_13705])).

cnf(c_26,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | ~ r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_338,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | ~ r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1010,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_14037,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK11,sK9) != iProver_top
    | r2_hidden(sK10,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_14028,c_1010])).

cnf(c_27,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | r2_hidden(sK11,sK9) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_48,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(sK11,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | r2_hidden(sK10,sK9) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(sK10,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | m1_subset_1(sK11,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14037,c_7371,c_48,c_47,c_46,c_45])).


%------------------------------------------------------------------------------
