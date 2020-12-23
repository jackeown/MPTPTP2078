%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1544+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:50 EST 2020

% Result     : Theorem 27.35s
% Output     : CNFRefutation 27.35s
% Verified   : 
% Statistics : Number of formulae       :  357 (2255 expanded)
%              Number of clauses        :  272 ( 545 expanded)
%              Number of leaves         :   25 ( 728 expanded)
%              Depth                    :   24
%              Number of atoms          : 2007 (33140 expanded)
%              Number of equality atoms :  591 (3875 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
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
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f34,plain,(
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
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f24])).

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
      | ~ sP2(X0,X2,X1) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X1,X4)
          & r1_orders_2(X0,X2,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k10_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
                & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
                & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
                & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
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
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f6])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | k13_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | k13_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | k13_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | k13_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | k13_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(X0,X3,X5)
                          | ~ r1_orders_2(X0,X2,X5)
                          | ~ r1_orders_2(X0,X1,X5)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | k13_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f42])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK13)
        & r1_orders_2(X0,X2,sK13)
        & r1_orders_2(X0,X1,sK13)
        & m1_subset_1(sK13,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,X2,X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X2,X3)
            | ~ r1_orders_2(X0,X1,X3)
            | k13_lattice3(X0,X1,X2) != X3 )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X3,X5)
                  | ~ r1_orders_2(X0,X2,X5)
                  | ~ r1_orders_2(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_orders_2(X0,X2,X3)
              & r1_orders_2(X0,X1,X3) )
            | k13_lattice3(X0,X1,X2) = X3 )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_orders_2(X0,sK12,X4)
              & r1_orders_2(X0,X2,X4)
              & r1_orders_2(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X2,sK12)
          | ~ r1_orders_2(X0,X1,sK12)
          | k13_lattice3(X0,X1,X2) != sK12 )
        & ( ( ! [X5] :
                ( r1_orders_2(X0,sK12,X5)
                | ~ r1_orders_2(X0,X2,X5)
                | ~ r1_orders_2(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_orders_2(X0,X2,sK12)
            & r1_orders_2(X0,X1,sK12) )
          | k13_lattice3(X0,X1,X2) = sK12 )
        & m1_subset_1(sK12,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r1_orders_2(X0,X1,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,X1,X3)
                | k13_lattice3(X0,X1,X2) != X3 )
              & ( ( ! [X5] :
                      ( r1_orders_2(X0,X3,X5)
                      | ~ r1_orders_2(X0,X2,X5)
                      | ~ r1_orders_2(X0,X1,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X3) )
                | k13_lattice3(X0,X1,X2) = X3 )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,sK11,X4)
                  & r1_orders_2(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK11,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | k13_lattice3(X0,X1,sK11) != X3 )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X3,X5)
                    | ~ r1_orders_2(X0,sK11,X5)
                    | ~ r1_orders_2(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,sK11,X3)
                & r1_orders_2(X0,X1,X3) )
              | k13_lattice3(X0,X1,sK11) = X3 )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK11,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | k13_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(X0,X3,X5)
                          | ~ r1_orders_2(X0,X2,X5)
                          | ~ r1_orders_2(X0,X1,X5)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | k13_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,sK10,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,sK10,X3)
                  | k13_lattice3(X0,sK10,X2) != X3 )
                & ( ( ! [X5] :
                        ( r1_orders_2(X0,X3,X5)
                        | ~ r1_orders_2(X0,X2,X5)
                        | ~ r1_orders_2(X0,sK10,X5)
                        | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,sK10,X3) )
                  | k13_lattice3(X0,sK10,X2) = X3 )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | k13_lattice3(X0,X1,X2) != X3 )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) = X3 )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(sK9,X3,X4)
                        & r1_orders_2(sK9,X2,X4)
                        & r1_orders_2(sK9,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(sK9)) )
                    | ~ r1_orders_2(sK9,X2,X3)
                    | ~ r1_orders_2(sK9,X1,X3)
                    | k13_lattice3(sK9,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(sK9,X3,X5)
                          | ~ r1_orders_2(sK9,X2,X5)
                          | ~ r1_orders_2(sK9,X1,X5)
                          | ~ m1_subset_1(X5,u1_struct_0(sK9)) )
                      & r1_orders_2(sK9,X2,X3)
                      & r1_orders_2(sK9,X1,X3) )
                    | k13_lattice3(sK9,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(sK9)) )
              & m1_subset_1(X2,u1_struct_0(sK9)) )
          & m1_subset_1(X1,u1_struct_0(sK9)) )
      & l1_orders_2(sK9)
      & v1_lattice3(sK9)
      & v5_orders_2(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ( ~ r1_orders_2(sK9,sK12,sK13)
        & r1_orders_2(sK9,sK11,sK13)
        & r1_orders_2(sK9,sK10,sK13)
        & m1_subset_1(sK13,u1_struct_0(sK9)) )
      | ~ r1_orders_2(sK9,sK11,sK12)
      | ~ r1_orders_2(sK9,sK10,sK12)
      | k13_lattice3(sK9,sK10,sK11) != sK12 )
    & ( ( ! [X5] :
            ( r1_orders_2(sK9,sK12,X5)
            | ~ r1_orders_2(sK9,sK11,X5)
            | ~ r1_orders_2(sK9,sK10,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK9)) )
        & r1_orders_2(sK9,sK11,sK12)
        & r1_orders_2(sK9,sK10,sK12) )
      | k13_lattice3(sK9,sK10,sK11) = sK12 )
    & m1_subset_1(sK12,u1_struct_0(sK9))
    & m1_subset_1(sK11,u1_struct_0(sK9))
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l1_orders_2(sK9)
    & v1_lattice3(sK9)
    & v5_orders_2(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f43,f48,f47,f46,f45,f44])).

fof(f80,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    v5_orders_2(sK9) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    v1_lattice3(sK9) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    ! [X5] :
      ( r1_orders_2(sK9,sK12,X5)
      | ~ r1_orders_2(sK9,sK11,X5)
      | ~ r1_orders_2(sK9,sK10,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK9))
      | k13_lattice3(sK9,sK10,sK11) = sK12 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X2,X1),X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f21,plain,(
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

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f32,plain,(
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
            ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK6(X0,X5,X6))
        & r1_orders_2(X0,X5,sK6(X0,X5,X6))
        & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
        & r1_orders_2(X0,X2,sK5(X0,X3))
        & r1_orders_2(X0,X1,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
                & r1_orders_2(X0,sK4(X0),X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK4(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                    & r1_orders_2(X0,sK3(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
                & r1_orders_2(X0,sK4(X0),sK5(X0,X3))
                & r1_orders_2(X0,sK3(X0),sK5(X0,X3))
                & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK4(X0),X3)
              | ~ r1_orders_2(X0,sK3(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK4(X0),u1_struct_0(X0))
          & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
                      | ~ r1_orders_2(X0,X6,X8)
                      | ~ r1_orders_2(X0,X5,X8)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X6,sK6(X0,X5,X6))
                  & r1_orders_2(X0,X5,sK6(X0,X5,X6))
                  & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f28,f32,f31,f30,f29])).

fof(f56,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK6(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
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

fof(f8,plain,(
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
    inference(rectify,[],[f3])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X0,X2,X1)
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
    inference(definition_folding,[],[f14,f24])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK8(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK8(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK8(X0,X1,X2,X3))
        & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,X3,sK8(X0,X1,X2,X3))
                    & r1_orders_2(X0,X2,sK8(X0,X1,X2,X3))
                    & r1_orders_2(X0,X1,sK8(X0,X1,X2,X3))
                    & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,sK8(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X2,X1)
      | r1_orders_2(X0,X2,sK8(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X2,X1)
      | m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X2,X1)
      | r1_orders_2(X0,X1,sK8(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK6(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X2,X1))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f83,plain,
    ( r1_orders_2(sK9,sK10,sK12)
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    m1_subset_1(sK12,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,
    ( r1_orders_2(sK9,sK11,sK12)
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,
    ( r1_orders_2(sK9,sK11,sK13)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | ~ r1_orders_2(sK9,sK10,sK12)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,
    ( r1_orders_2(sK9,sK10,sK13)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | ~ r1_orders_2(sK9,sK10,sK12)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,
    ( m1_subset_1(sK13,u1_struct_0(sK9))
    | ~ r1_orders_2(sK9,sK11,sK12)
    | ~ r1_orders_2(sK9,sK10,sK12)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,
    ( ~ r1_orders_2(sK9,sK12,sK13)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | ~ r1_orders_2(sK9,sK10,sK12)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f12,f22,f21])).

fof(f63,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_16,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4874,plain,
    ( ~ sP2(X0_52,X0_50,X1_50)
    | ~ r1_orders_2(X0_52,X0_50,X2_50)
    | ~ r1_orders_2(X0_52,X1_50,X2_50)
    | r1_orders_2(X0_52,X1_50,sK7(X0_52,X0_50,X1_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_52))
    | k10_lattice3(X0_52,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_5464,plain,
    ( k10_lattice3(X0_52,X0_50,X1_50) = X2_50
    | sP2(X0_52,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_52,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_52,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_52,X0_50,sK7(X0_52,X1_50,X0_50,X2_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4874])).

cnf(c_15,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4875,plain,
    ( ~ sP2(X0_52,X0_50,X1_50)
    | ~ r1_orders_2(X0_52,X0_50,X2_50)
    | ~ r1_orders_2(X0_52,X1_50,X2_50)
    | r1_orders_2(X0_52,X0_50,sK7(X0_52,X0_50,X1_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_52))
    | k10_lattice3(X0_52,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_5463,plain,
    ( k10_lattice3(X0_52,X0_50,X1_50) = X2_50
    | sP2(X0_52,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_52,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_52,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_52,X1_50,sK7(X0_52,X1_50,X0_50,X2_50)) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4875])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4860,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_5478,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4860])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4861,negated_conjecture,
    ( m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_5477,plain,
    ( m1_subset_1(sK11,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4861])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_39,negated_conjecture,
    ( v5_orders_2(sK9) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k13_lattice3(X1,X0,X2)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_39])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ v1_lattice3(sK9)
    | ~ l1_orders_2(sK9)
    | k13_lattice3(sK9,X1,X0) = k13_lattice3(sK9,X0,X1) ),
    inference(unflattening,[status(thm)],[c_721])).

cnf(c_38,negated_conjecture,
    ( v1_lattice3(sK9) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k13_lattice3(X1,X0,X2)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_38])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ v5_orders_2(sK9)
    | ~ l1_orders_2(sK9)
    | k13_lattice3(sK9,X1,X0) = k13_lattice3(sK9,X0,X1) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_37,negated_conjecture,
    ( l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k13_lattice3(sK9,X1,X0) = k13_lattice3(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_39,c_37])).

cnf(c_724,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k13_lattice3(sK9,X1,X0) = k13_lattice3(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_39,c_37,c_537])).

cnf(c_4857,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | k13_lattice3(sK9,X1_50,X0_50) = k13_lattice3(sK9,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_724])).

cnf(c_5481,plain,
    ( k13_lattice3(sK9,X0_50,X1_50) = k13_lattice3(sK9,X1_50,X0_50)
    | m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4857])).

cnf(c_7232,plain,
    ( k13_lattice3(sK9,X0_50,sK11) = k13_lattice3(sK9,sK11,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5477,c_5481])).

cnf(c_8106,plain,
    ( k13_lattice3(sK9,sK11,sK10) = k13_lattice3(sK9,sK10,sK11) ),
    inference(superposition,[status(thm)],[c_5478,c_7232])).

cnf(c_31,negated_conjecture,
    ( ~ r1_orders_2(sK9,sK10,X0)
    | ~ r1_orders_2(sK9,sK11,X0)
    | r1_orders_2(sK9,sK12,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4865,negated_conjecture,
    ( ~ r1_orders_2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,sK11,X0_50)
    | r1_orders_2(sK9,sK12,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_5473,plain,
    ( k13_lattice3(sK9,sK10,sK11) = sK12
    | r1_orders_2(sK9,sK10,X0_50) != iProver_top
    | r1_orders_2(sK9,sK11,X0_50) != iProver_top
    | r1_orders_2(sK9,sK12,X0_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4865])).

cnf(c_8142,plain,
    ( k13_lattice3(sK9,sK11,sK10) = sK12
    | r1_orders_2(sK9,sK10,X0_50) != iProver_top
    | r1_orders_2(sK9,sK11,X0_50) != iProver_top
    | r1_orders_2(sK9,sK12,X0_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8106,c_5473])).

cnf(c_9219,plain,
    ( k10_lattice3(sK9,X0_50,sK10) = X1_50
    | k13_lattice3(sK9,sK11,sK10) = sK12
    | sP2(sK9,sK10,X0_50) != iProver_top
    | r1_orders_2(sK9,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK9,sK10,X1_50) != iProver_top
    | r1_orders_2(sK9,sK11,sK7(sK9,sK10,X0_50,X1_50)) != iProver_top
    | r1_orders_2(sK9,sK12,sK7(sK9,sK10,X0_50,X1_50)) = iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK7(sK9,sK10,X0_50,X1_50),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5463,c_8142])).

cnf(c_17,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4873,plain,
    ( ~ sP2(X0_52,X0_50,X1_50)
    | ~ r1_orders_2(X0_52,X0_50,X2_50)
    | ~ r1_orders_2(X0_52,X1_50,X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_52))
    | m1_subset_1(sK7(X0_52,X0_50,X1_50,X2_50),u1_struct_0(X0_52))
    | k10_lattice3(X0_52,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_22952,plain,
    ( ~ sP2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,sK10,X1_50)
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | m1_subset_1(sK7(sK9,sK10,X0_50,X1_50),u1_struct_0(sK9))
    | k10_lattice3(sK9,X0_50,sK10) = X1_50 ),
    inference(instantiation,[status(thm)],[c_4873])).

cnf(c_22954,plain,
    ( k10_lattice3(sK9,X0_50,sK10) = X1_50
    | sP2(sK9,sK10,X0_50) != iProver_top
    | r1_orders_2(sK9,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK9,sK10,X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK7(sK9,sK10,X0_50,X1_50),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22952])).

cnf(c_128083,plain,
    ( m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top
    | r1_orders_2(sK9,sK12,sK7(sK9,sK10,X0_50,X1_50)) = iProver_top
    | r1_orders_2(sK9,sK11,sK7(sK9,sK10,X0_50,X1_50)) != iProver_top
    | r1_orders_2(sK9,sK10,X1_50) != iProver_top
    | r1_orders_2(sK9,X0_50,X1_50) != iProver_top
    | sP2(sK9,sK10,X0_50) != iProver_top
    | k13_lattice3(sK9,sK11,sK10) = sK12
    | k10_lattice3(sK9,X0_50,sK10) = X1_50 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9219,c_22954])).

cnf(c_128084,plain,
    ( k10_lattice3(sK9,X0_50,sK10) = X1_50
    | k13_lattice3(sK9,sK11,sK10) = sK12
    | sP2(sK9,sK10,X0_50) != iProver_top
    | r1_orders_2(sK9,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK9,sK10,X1_50) != iProver_top
    | r1_orders_2(sK9,sK11,sK7(sK9,sK10,X0_50,X1_50)) != iProver_top
    | r1_orders_2(sK9,sK12,sK7(sK9,sK10,X0_50,X1_50)) = iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_128083])).

cnf(c_128097,plain,
    ( k10_lattice3(sK9,sK11,sK10) = X0_50
    | k13_lattice3(sK9,sK11,sK10) = sK12
    | sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,sK10,X0_50) != iProver_top
    | r1_orders_2(sK9,sK11,X0_50) != iProver_top
    | r1_orders_2(sK9,sK12,sK7(sK9,sK10,sK11,X0_50)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5464,c_128084])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_39])).

cnf(c_705,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ v1_lattice3(sK9)
    | ~ l1_orders_2(sK9)
    | k10_lattice3(sK9,X1,X0) = k13_lattice3(sK9,X1,X0) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ v5_orders_2(sK9)
    | ~ l1_orders_2(sK9)
    | k10_lattice3(sK9,X1,X0) = k13_lattice3(sK9,X1,X0) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k10_lattice3(sK9,X1,X0) = k13_lattice3(sK9,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_39,c_37])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k10_lattice3(sK9,X1,X0) = k13_lattice3(sK9,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_705,c_39,c_37,c_516])).

cnf(c_4858,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | k10_lattice3(sK9,X1_50,X0_50) = k13_lattice3(sK9,X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_707])).

cnf(c_5480,plain,
    ( k10_lattice3(sK9,X0_50,X1_50) = k13_lattice3(sK9,X0_50,X1_50)
    | m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4858])).

cnf(c_6183,plain,
    ( k10_lattice3(sK9,sK11,X0_50) = k13_lattice3(sK9,sK11,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5477,c_5480])).

cnf(c_6398,plain,
    ( k10_lattice3(sK9,sK11,sK10) = k13_lattice3(sK9,sK11,sK10) ),
    inference(superposition,[status(thm)],[c_5478,c_6183])).

cnf(c_128098,plain,
    ( k13_lattice3(sK9,sK11,sK10) = X0_50
    | k13_lattice3(sK9,sK11,sK10) = sK12
    | sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,sK10,X0_50) != iProver_top
    | r1_orders_2(sK9,sK11,X0_50) != iProver_top
    | r1_orders_2(sK9,sK12,sK7(sK9,sK10,sK11,X0_50)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_128097,c_6398])).

cnf(c_128100,plain,
    ( k13_lattice3(sK9,sK11,sK10) = sK12
    | sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top
    | r1_orders_2(sK9,sK12,sK7(sK9,sK10,sK11,sK12)) = iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_128098])).

cnf(c_4892,plain,
    ( ~ r1_orders_2(X0_52,X0_50,X1_50)
    | r1_orders_2(X0_52,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_117762,plain,
    ( ~ r1_orders_2(sK9,X0_50,X1_50)
    | r1_orders_2(sK9,X2_50,sK13)
    | X2_50 != X0_50
    | sK13 != X1_50 ),
    inference(instantiation,[status(thm)],[c_4892])).

cnf(c_117810,plain,
    ( ~ r1_orders_2(sK9,X0_50,sK13)
    | r1_orders_2(sK9,X1_50,sK13)
    | X1_50 != X0_50
    | sK13 != sK13 ),
    inference(instantiation,[status(thm)],[c_117762])).

cnf(c_118570,plain,
    ( r1_orders_2(sK9,X0_50,sK13)
    | ~ r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),sK13)
    | X0_50 != k10_lattice3(sK9,sK11,sK10)
    | sK13 != sK13 ),
    inference(instantiation,[status(thm)],[c_117810])).

cnf(c_118604,plain,
    ( X0_50 != k10_lattice3(sK9,sK11,sK10)
    | sK13 != sK13
    | r1_orders_2(sK9,X0_50,sK13) = iProver_top
    | r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118570])).

cnf(c_118606,plain,
    ( sK13 != sK13
    | sK12 != k10_lattice3(sK9,sK11,sK10)
    | r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),sK13) != iProver_top
    | r1_orders_2(sK9,sK12,sK13) = iProver_top ),
    inference(instantiation,[status(thm)],[c_118604])).

cnf(c_18,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,k10_lattice3(X0,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4872,plain,
    ( ~ sP2(X0_52,X0_50,X1_50)
    | ~ r1_orders_2(X0_52,X0_50,X2_50)
    | ~ r1_orders_2(X0_52,X1_50,X2_50)
    | r1_orders_2(X0_52,k10_lattice3(X0_52,X1_50,X0_50),X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_52))
    | ~ m1_subset_1(k10_lattice3(X0_52,X1_50,X0_50),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_117766,plain,
    ( ~ sP2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,X0_50,sK13)
    | ~ r1_orders_2(sK9,X1_50,sK13)
    | r1_orders_2(sK9,k10_lattice3(sK9,X1_50,X0_50),sK13)
    | ~ m1_subset_1(k10_lattice3(sK9,X1_50,X0_50),u1_struct_0(sK9))
    | ~ m1_subset_1(sK13,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4872])).

cnf(c_117831,plain,
    ( ~ sP2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,X0_50,sK13)
    | r1_orders_2(sK9,k10_lattice3(sK9,X0_50,sK10),sK13)
    | ~ r1_orders_2(sK9,sK10,sK13)
    | ~ m1_subset_1(k10_lattice3(sK9,X0_50,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK13,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_117766])).

cnf(c_118272,plain,
    ( ~ sP2(sK9,sK10,sK11)
    | r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),sK13)
    | ~ r1_orders_2(sK9,sK10,sK13)
    | ~ r1_orders_2(sK9,sK11,sK13)
    | ~ m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK13,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_117831])).

cnf(c_118273,plain,
    ( sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),sK13) = iProver_top
    | r1_orders_2(sK9,sK10,sK13) != iProver_top
    | r1_orders_2(sK9,sK11,sK13) != iProver_top
    | m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK13,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118272])).

cnf(c_11085,plain,
    ( r1_orders_2(X0_52,X0_50,X1_50)
    | ~ r1_orders_2(X0_52,X2_50,k10_lattice3(X0_52,X2_50,X3_50))
    | X0_50 != X2_50
    | X1_50 != k10_lattice3(X0_52,X2_50,X3_50) ),
    inference(instantiation,[status(thm)],[c_4892])).

cnf(c_14077,plain,
    ( r1_orders_2(sK9,X0_50,sK12)
    | ~ r1_orders_2(sK9,sK11,k10_lattice3(sK9,sK11,sK10))
    | X0_50 != sK11
    | sK12 != k10_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_11085])).

cnf(c_112691,plain,
    ( ~ r1_orders_2(sK9,sK11,k10_lattice3(sK9,sK11,sK10))
    | r1_orders_2(sK9,sK11,sK12)
    | sK11 != sK11
    | sK12 != k10_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_14077])).

cnf(c_112692,plain,
    ( sK11 != sK11
    | sK12 != k10_lattice3(sK9,sK11,sK10)
    | r1_orders_2(sK9,sK11,k10_lattice3(sK9,sK11,sK10)) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_112691])).

cnf(c_12573,plain,
    ( ~ sP2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,X1_50,X2_50)
    | ~ r1_orders_2(sK9,X0_50,X2_50)
    | r1_orders_2(sK9,k10_lattice3(sK9,X1_50,X0_50),X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(sK9))
    | ~ m1_subset_1(k10_lattice3(sK9,X1_50,X0_50),u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4872])).

cnf(c_20035,plain,
    ( ~ sP2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,X0_50,sK12)
    | ~ r1_orders_2(sK9,X1_50,sK12)
    | r1_orders_2(sK9,k10_lattice3(sK9,X1_50,X0_50),sK12)
    | ~ m1_subset_1(k10_lattice3(sK9,X1_50,X0_50),u1_struct_0(sK9))
    | ~ m1_subset_1(sK12,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_12573])).

cnf(c_23336,plain,
    ( ~ sP2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,X0_50,sK12)
    | r1_orders_2(sK9,k10_lattice3(sK9,X0_50,sK10),sK12)
    | ~ r1_orders_2(sK9,sK10,sK12)
    | ~ m1_subset_1(k10_lattice3(sK9,X0_50,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK12,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_20035])).

cnf(c_93098,plain,
    ( ~ sP2(sK9,sK10,sK11)
    | r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),sK12)
    | ~ r1_orders_2(sK9,sK10,sK12)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | ~ m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK12,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_23336])).

cnf(c_93099,plain,
    ( sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),sK12) = iProver_top
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top
    | m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_93098])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK6(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4880,plain,
    ( ~ r1_orders_2(X0_52,X0_50,X1_50)
    | ~ r1_orders_2(X0_52,X2_50,X1_50)
    | r1_orders_2(X0_52,sK6(X0_52,X2_50,X0_50),X1_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_12595,plain,
    ( ~ r1_orders_2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,X2_50,X1_50)
    | r1_orders_2(sK9,sK6(sK9,X2_50,X0_50),X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_4880])).

cnf(c_35329,plain,
    ( ~ r1_orders_2(sK9,X0_50,X1_50)
    | r1_orders_2(sK9,sK6(sK9,X0_50,sK10),X1_50)
    | ~ r1_orders_2(sK9,sK10,X1_50)
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_12595])).

cnf(c_76466,plain,
    ( r1_orders_2(sK9,sK6(sK9,sK11,sK10),sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)))
    | ~ r1_orders_2(sK9,sK10,sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)))
    | ~ r1_orders_2(sK9,sK11,sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)))
    | ~ m1_subset_1(sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_35329])).

cnf(c_76478,plain,
    ( r1_orders_2(sK9,sK6(sK9,sK11,sK10),sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10))) = iProver_top
    | r1_orders_2(sK9,sK10,sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10))) != iProver_top
    | r1_orders_2(sK9,sK11,sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10))) != iProver_top
    | m1_subset_1(sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top
    | sP0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76466])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4877,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_52))
    | m1_subset_1(sK6(X0_52,X1_50,X0_50),u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_23143,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | m1_subset_1(sK6(sK9,sK11,X0_50),u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_4877])).

cnf(c_55400,plain,
    ( m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_23143])).

cnf(c_55414,plain,
    ( m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top
    | sP0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55400])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4878,plain,
    ( r1_orders_2(X0_52,X0_50,sK6(X0_52,X0_50,X1_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_11174,plain,
    ( r1_orders_2(sK9,sK11,sK6(sK9,sK11,X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_4878])).

cnf(c_32443,plain,
    ( r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_11174])).

cnf(c_32444,plain,
    ( r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top
    | sP0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32443])).

cnf(c_21,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X3,sK8(X0,X2,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_671,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X3,sK8(X0,X2,X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_672,plain,
    ( sP2(sK9,X0,X1)
    | ~ r1_orders_2(sK9,X1,X2)
    | ~ r1_orders_2(sK9,X0,X2)
    | ~ r1_orders_2(sK9,X2,sK8(sK9,X1,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_676,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r1_orders_2(sK9,X2,sK8(sK9,X1,X0,X2))
    | ~ r1_orders_2(sK9,X0,X2)
    | ~ r1_orders_2(sK9,X1,X2)
    | sP2(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_37])).

cnf(c_677,plain,
    ( sP2(sK9,X0,X1)
    | ~ r1_orders_2(sK9,X1,X2)
    | ~ r1_orders_2(sK9,X0,X2)
    | ~ r1_orders_2(sK9,X2,sK8(sK9,X1,X0,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9)) ),
    inference(renaming,[status(thm)],[c_676])).

cnf(c_4853,plain,
    ( sP2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,X1_50,X2_50)
    | ~ r1_orders_2(sK9,X0_50,X2_50)
    | ~ r1_orders_2(sK9,X2_50,sK8(sK9,X1_50,X0_50,X2_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_677])).

cnf(c_9683,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,X0_50,sK8(sK9,sK11,sK10,X0_50))
    | ~ r1_orders_2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,sK11,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4853])).

cnf(c_13870,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK6(sK9,sK11,X0_50),sK8(sK9,sK11,sK10,sK6(sK9,sK11,X0_50)))
    | ~ r1_orders_2(sK9,sK10,sK6(sK9,sK11,X0_50))
    | ~ r1_orders_2(sK9,sK11,sK6(sK9,sK11,X0_50))
    | ~ m1_subset_1(sK6(sK9,sK11,X0_50),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_9683])).

cnf(c_32411,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK6(sK9,sK11,sK10),sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)))
    | ~ r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10))
    | ~ r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10))
    | ~ m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_13870])).

cnf(c_32431,plain,
    ( sP2(sK9,sK10,sK11) = iProver_top
    | r1_orders_2(sK9,sK6(sK9,sK11,sK10),sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10))) != iProver_top
    | r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10)) != iProver_top
    | r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10)) != iProver_top
    | m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32411])).

cnf(c_22,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,sK8(X0,X2,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_642,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,sK8(X0,X2,X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_39])).

cnf(c_643,plain,
    ( sP2(sK9,X0,X1)
    | ~ r1_orders_2(sK9,X1,X2)
    | ~ r1_orders_2(sK9,X0,X2)
    | r1_orders_2(sK9,X0,sK8(sK9,X1,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | r1_orders_2(sK9,X0,sK8(sK9,X1,X0,X2))
    | ~ r1_orders_2(sK9,X0,X2)
    | ~ r1_orders_2(sK9,X1,X2)
    | sP2(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_37])).

cnf(c_646,plain,
    ( sP2(sK9,X0,X1)
    | ~ r1_orders_2(sK9,X1,X2)
    | ~ r1_orders_2(sK9,X0,X2)
    | r1_orders_2(sK9,X0,sK8(sK9,X1,X0,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9)) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_4854,plain,
    ( sP2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,X1_50,X2_50)
    | ~ r1_orders_2(sK9,X0_50,X2_50)
    | r1_orders_2(sK9,X0_50,sK8(sK9,X1_50,X0_50,X2_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_646])).

cnf(c_9682,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK10,X0_50)
    | r1_orders_2(sK9,sK10,sK8(sK9,sK11,sK10,X0_50))
    | ~ r1_orders_2(sK9,sK11,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4854])).

cnf(c_13875,plain,
    ( sP2(sK9,sK10,sK11)
    | r1_orders_2(sK9,sK10,sK8(sK9,sK11,sK10,sK6(sK9,sK11,X0_50)))
    | ~ r1_orders_2(sK9,sK10,sK6(sK9,sK11,X0_50))
    | ~ r1_orders_2(sK9,sK11,sK6(sK9,sK11,X0_50))
    | ~ m1_subset_1(sK6(sK9,sK11,X0_50),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_9682])).

cnf(c_32413,plain,
    ( sP2(sK9,sK10,sK11)
    | r1_orders_2(sK9,sK10,sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)))
    | ~ r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10))
    | ~ r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10))
    | ~ m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_13875])).

cnf(c_32427,plain,
    ( sP2(sK9,sK10,sK11) = iProver_top
    | r1_orders_2(sK9,sK10,sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10))) = iProver_top
    | r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10)) != iProver_top
    | r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10)) != iProver_top
    | m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32413])).

cnf(c_24,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK8(X0,X2,X1,X3),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_576,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK8(X0,X2,X1,X3),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_577,plain,
    ( sP2(sK9,X0,X1)
    | ~ r1_orders_2(sK9,X1,X2)
    | ~ r1_orders_2(sK9,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | m1_subset_1(sK8(sK9,X1,X0,X2),u1_struct_0(sK9))
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_581,plain,
    ( m1_subset_1(sK8(sK9,X1,X0,X2),u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r1_orders_2(sK9,X0,X2)
    | ~ r1_orders_2(sK9,X1,X2)
    | sP2(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_37])).

cnf(c_582,plain,
    ( sP2(sK9,X0,X1)
    | ~ r1_orders_2(sK9,X1,X2)
    | ~ r1_orders_2(sK9,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | m1_subset_1(sK8(sK9,X1,X0,X2),u1_struct_0(sK9)) ),
    inference(renaming,[status(thm)],[c_581])).

cnf(c_4856,plain,
    ( sP2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,X1_50,X2_50)
    | ~ r1_orders_2(sK9,X0_50,X2_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK9))
    | m1_subset_1(sK8(sK9,X1_50,X0_50,X2_50),u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_582])).

cnf(c_9684,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,sK11,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | m1_subset_1(sK8(sK9,sK11,sK10,X0_50),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4856])).

cnf(c_13874,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK10,sK6(sK9,sK11,X0_50))
    | ~ r1_orders_2(sK9,sK11,sK6(sK9,sK11,X0_50))
    | m1_subset_1(sK8(sK9,sK11,sK10,sK6(sK9,sK11,X0_50)),u1_struct_0(sK9))
    | ~ m1_subset_1(sK6(sK9,sK11,X0_50),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_9684])).

cnf(c_32414,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10))
    | ~ r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10))
    | m1_subset_1(sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)),u1_struct_0(sK9))
    | ~ m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_13874])).

cnf(c_32425,plain,
    ( sP2(sK9,sK10,sK11) = iProver_top
    | r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10)) != iProver_top
    | r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10)) != iProver_top
    | m1_subset_1(sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)),u1_struct_0(sK9)) = iProver_top
    | m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32414])).

cnf(c_22337,plain,
    ( r1_orders_2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK10,sK11))
    | X1_50 != k13_lattice3(sK9,sK10,sK11)
    | X0_50 != sK10 ),
    inference(instantiation,[status(thm)],[c_4892])).

cnf(c_27153,plain,
    ( r1_orders_2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK10,sK11))
    | X0_50 != k13_lattice3(sK9,sK10,sK11)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_22337])).

cnf(c_27154,plain,
    ( X0_50 != k13_lattice3(sK9,sK10,sK11)
    | sK10 != sK10
    | r1_orders_2(sK9,sK10,X0_50) = iProver_top
    | r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK10,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27153])).

cnf(c_27156,plain,
    ( sK10 != sK10
    | sK12 != k13_lattice3(sK9,sK10,sK11)
    | r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK10,sK11)) != iProver_top
    | r1_orders_2(sK9,sK10,sK12) = iProver_top ),
    inference(instantiation,[status(thm)],[c_27154])).

cnf(c_8592,plain,
    ( ~ r1_orders_2(X0_52,X0_50,X1_50)
    | r1_orders_2(X0_52,X2_50,k13_lattice3(sK9,sK10,sK11))
    | X2_50 != X0_50
    | k13_lattice3(sK9,sK10,sK11) != X1_50 ),
    inference(instantiation,[status(thm)],[c_4892])).

cnf(c_22440,plain,
    ( r1_orders_2(sK9,X0_50,k13_lattice3(sK9,sK10,sK11))
    | ~ r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK11,sK10))
    | X0_50 != sK10
    | k13_lattice3(sK9,sK10,sK11) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_8592])).

cnf(c_26680,plain,
    ( r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK10,sK11))
    | ~ r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK11,sK10))
    | k13_lattice3(sK9,sK10,sK11) != k13_lattice3(sK9,sK11,sK10)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_22440])).

cnf(c_26681,plain,
    ( k13_lattice3(sK9,sK10,sK11) != k13_lattice3(sK9,sK11,sK10)
    | sK10 != sK10
    | r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK10,sK11)) = iProver_top
    | r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26680])).

cnf(c_23,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X2,sK8(X0,X2,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_609,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X2,sK8(X0,X2,X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_610,plain,
    ( sP2(sK9,X0,X1)
    | ~ r1_orders_2(sK9,X1,X2)
    | ~ r1_orders_2(sK9,X0,X2)
    | r1_orders_2(sK9,X1,sK8(sK9,X1,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | r1_orders_2(sK9,X1,sK8(sK9,X1,X0,X2))
    | ~ r1_orders_2(sK9,X0,X2)
    | ~ r1_orders_2(sK9,X1,X2)
    | sP2(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_37])).

cnf(c_615,plain,
    ( sP2(sK9,X0,X1)
    | ~ r1_orders_2(sK9,X1,X2)
    | ~ r1_orders_2(sK9,X0,X2)
    | r1_orders_2(sK9,X1,sK8(sK9,X1,X0,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9)) ),
    inference(renaming,[status(thm)],[c_614])).

cnf(c_4855,plain,
    ( sP2(sK9,X0_50,X1_50)
    | ~ r1_orders_2(sK9,X1_50,X2_50)
    | ~ r1_orders_2(sK9,X0_50,X2_50)
    | r1_orders_2(sK9,X1_50,sK8(sK9,X1_50,X0_50,X2_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_615])).

cnf(c_9681,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,sK11,X0_50)
    | r1_orders_2(sK9,sK11,sK8(sK9,sK11,sK10,X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4855])).

cnf(c_11173,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK10,sK6(sK9,sK11,X0_50))
    | r1_orders_2(sK9,sK11,sK8(sK9,sK11,sK10,sK6(sK9,sK11,X0_50)))
    | ~ r1_orders_2(sK9,sK11,sK6(sK9,sK11,X0_50))
    | ~ m1_subset_1(sK6(sK9,sK11,X0_50),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_9681])).

cnf(c_17829,plain,
    ( sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10))
    | r1_orders_2(sK9,sK11,sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10)))
    | ~ r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10))
    | ~ m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_11173])).

cnf(c_17832,plain,
    ( sP2(sK9,sK10,sK11) = iProver_top
    | r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10)) != iProver_top
    | r1_orders_2(sK9,sK11,sK8(sK9,sK11,sK10,sK6(sK9,sK11,sK10))) = iProver_top
    | r1_orders_2(sK9,sK11,sK6(sK9,sK11,sK10)) != iProver_top
    | m1_subset_1(sK6(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17829])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4879,plain,
    ( r1_orders_2(X0_52,X0_50,sK6(X0_52,X1_50,X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_12589,plain,
    ( r1_orders_2(sK9,X0_50,sK6(sK9,X1_50,X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_4879])).

cnf(c_17828,plain,
    ( r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | ~ sP0(sK9) ),
    inference(instantiation,[status(thm)],[c_12589])).

cnf(c_17830,plain,
    ( r1_orders_2(sK9,sK10,sK6(sK9,sK11,sK10)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top
    | sP0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17828])).

cnf(c_4889,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_7516,plain,
    ( X0_50 != X1_50
    | k10_lattice3(sK9,sK11,sK10) != X1_50
    | k10_lattice3(sK9,sK11,sK10) = X0_50 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_17241,plain,
    ( k10_lattice3(X0_52,X0_50,X1_50) != X2_50
    | k10_lattice3(sK9,sK11,sK10) != X2_50
    | k10_lattice3(sK9,sK11,sK10) = k10_lattice3(X0_52,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_7516])).

cnf(c_17243,plain,
    ( k10_lattice3(sK9,sK11,sK10) = k10_lattice3(sK9,sK12,sK12)
    | k10_lattice3(sK9,sK11,sK10) != sK12
    | k10_lattice3(sK9,sK12,sK12) != sK12 ),
    inference(instantiation,[status(thm)],[c_17241])).

cnf(c_6072,plain,
    ( X0_50 != X1_50
    | X0_50 = k13_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK11,sK10) != X1_50 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_17024,plain,
    ( k10_lattice3(X0_52,X0_50,X1_50) != X2_50
    | k10_lattice3(X0_52,X0_50,X1_50) = k13_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK11,sK10) != X2_50 ),
    inference(instantiation,[status(thm)],[c_6072])).

cnf(c_17025,plain,
    ( k10_lattice3(sK9,sK12,sK12) = k13_lattice3(sK9,sK11,sK10)
    | k10_lattice3(sK9,sK12,sK12) != sK12
    | k13_lattice3(sK9,sK11,sK10) != sK12 ),
    inference(instantiation,[status(thm)],[c_17024])).

cnf(c_11093,plain,
    ( r1_orders_2(X0_52,X0_50,X1_50)
    | ~ r1_orders_2(X0_52,k10_lattice3(X0_52,X2_50,X3_50),X4_50)
    | X1_50 != X4_50
    | X0_50 != k10_lattice3(X0_52,X2_50,X3_50) ),
    inference(instantiation,[status(thm)],[c_4892])).

cnf(c_14714,plain,
    ( ~ r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),X0_50)
    | r1_orders_2(sK9,sK12,X1_50)
    | X1_50 != X0_50
    | sK12 != k10_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_11093])).

cnf(c_14715,plain,
    ( X0_50 != X1_50
    | sK12 != k10_lattice3(sK9,sK11,sK10)
    | r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),X1_50) != iProver_top
    | r1_orders_2(sK9,sK12,X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14714])).

cnf(c_14717,plain,
    ( sK12 != k10_lattice3(sK9,sK11,sK10)
    | sK12 != sK12
    | r1_orders_2(sK9,k10_lattice3(sK9,sK11,sK10),sK12) != iProver_top
    | r1_orders_2(sK9,sK12,sK12) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14715])).

cnf(c_6611,plain,
    ( X0_50 != X1_50
    | X0_50 = k13_lattice3(sK9,X2_50,X3_50)
    | k13_lattice3(sK9,X2_50,X3_50) != X1_50 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_7632,plain,
    ( X0_50 != k10_lattice3(sK9,X1_50,X2_50)
    | X0_50 = k13_lattice3(sK9,X2_50,X1_50)
    | k13_lattice3(sK9,X2_50,X1_50) != k10_lattice3(sK9,X1_50,X2_50) ),
    inference(instantiation,[status(thm)],[c_6611])).

cnf(c_12458,plain,
    ( k10_lattice3(sK9,sK11,sK10) != k10_lattice3(sK9,X0_50,X1_50)
    | k10_lattice3(sK9,sK11,sK10) = k13_lattice3(sK9,X1_50,X0_50)
    | k13_lattice3(sK9,X1_50,X0_50) != k10_lattice3(sK9,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_7632])).

cnf(c_12464,plain,
    ( k10_lattice3(sK9,sK11,sK10) != k10_lattice3(sK9,sK12,sK12)
    | k10_lattice3(sK9,sK11,sK10) = k13_lattice3(sK9,sK12,sK12)
    | k13_lattice3(sK9,sK12,sK12) != k10_lattice3(sK9,sK12,sK12) ),
    inference(instantiation,[status(thm)],[c_12458])).

cnf(c_9361,plain,
    ( X0_50 != k13_lattice3(sK9,sK11,sK10)
    | k10_lattice3(sK9,sK11,sK10) = X0_50
    | k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_7516])).

cnf(c_12455,plain,
    ( k10_lattice3(sK9,X0_50,X1_50) != k13_lattice3(sK9,sK11,sK10)
    | k10_lattice3(sK9,sK11,sK10) = k10_lattice3(sK9,X0_50,X1_50)
    | k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_9361])).

cnf(c_12462,plain,
    ( k10_lattice3(sK9,sK11,sK10) = k10_lattice3(sK9,sK12,sK12)
    | k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK11,sK10)
    | k10_lattice3(sK9,sK12,sK12) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_12455])).

cnf(c_20,plain,
    ( ~ sP2(X0,X1,X2)
    | r1_orders_2(X0,X2,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4870,plain,
    ( ~ sP2(X0_52,X0_50,X1_50)
    | r1_orders_2(X0_52,X1_50,k10_lattice3(X0_52,X1_50,X0_50))
    | ~ m1_subset_1(k10_lattice3(X0_52,X1_50,X0_50),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_10343,plain,
    ( ~ sP2(sK9,sK10,sK11)
    | r1_orders_2(sK9,sK11,k10_lattice3(sK9,sK11,sK10))
    | ~ m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4870])).

cnf(c_10348,plain,
    ( sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,sK11,k10_lattice3(sK9,sK11,sK10)) = iProver_top
    | m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10343])).

cnf(c_5483,plain,
    ( sP2(sK9,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK9,X1_50,X2_50) != iProver_top
    | r1_orders_2(sK9,X0_50,X2_50) != iProver_top
    | r1_orders_2(sK9,X1_50,sK8(sK9,X1_50,X0_50,X2_50)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4855])).

cnf(c_5485,plain,
    ( sP2(sK9,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK9,X1_50,X2_50) != iProver_top
    | r1_orders_2(sK9,X0_50,X2_50) != iProver_top
    | r1_orders_2(sK9,X2_50,sK8(sK9,X1_50,X0_50,X2_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4853])).

cnf(c_9555,plain,
    ( sP2(sK9,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK9,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK9,X1_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_5485])).

cnf(c_9588,plain,
    ( sP2(sK9,sK12,sK12) = iProver_top
    | r1_orders_2(sK9,sK12,sK12) != iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9555])).

cnf(c_33,negated_conjecture,
    ( r1_orders_2(sK9,sK10,sK12)
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4863,negated_conjecture,
    ( r1_orders_2(sK9,sK10,sK12)
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_5475,plain,
    ( k13_lattice3(sK9,sK10,sK11) = sK12
    | r1_orders_2(sK9,sK10,sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4863])).

cnf(c_6041,plain,
    ( k13_lattice3(sK9,sK10,sK11) = sK12
    | r1_orders_2(sK9,sK11,sK12) != iProver_top
    | r1_orders_2(sK9,sK12,sK12) = iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5475,c_5473])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK12,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_45,plain,
    ( m1_subset_1(sK12,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( r1_orders_2(sK9,sK11,sK12)
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4864,negated_conjecture,
    ( r1_orders_2(sK9,sK11,sK12)
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_4938,plain,
    ( k13_lattice3(sK9,sK10,sK11) = sK12
    | r1_orders_2(sK9,sK11,sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4864])).

cnf(c_9202,plain,
    ( r1_orders_2(sK9,sK12,sK12) = iProver_top
    | k13_lattice3(sK9,sK10,sK11) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6041,c_45,c_4938])).

cnf(c_9203,plain,
    ( k13_lattice3(sK9,sK10,sK11) = sK12
    | r1_orders_2(sK9,sK12,sK12) = iProver_top ),
    inference(renaming,[status(thm)],[c_9202])).

cnf(c_14,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k10_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4876,plain,
    ( ~ sP2(X0_52,X0_50,X1_50)
    | ~ r1_orders_2(X0_52,X0_50,X2_50)
    | ~ r1_orders_2(X0_52,X1_50,X2_50)
    | ~ r1_orders_2(X0_52,X2_50,sK7(X0_52,X0_50,X1_50,X2_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_52))
    | k10_lattice3(X0_52,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_5462,plain,
    ( k10_lattice3(X0_52,X0_50,X1_50) = X2_50
    | sP2(X0_52,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_52,X0_50,X2_50) != iProver_top
    | r1_orders_2(X0_52,X1_50,X2_50) != iProver_top
    | r1_orders_2(X0_52,X2_50,sK7(X0_52,X1_50,X0_50,X2_50)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4876])).

cnf(c_8637,plain,
    ( k10_lattice3(X0_52,X0_50,X1_50) = X1_50
    | sP2(X0_52,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_52,X0_50,X1_50) != iProver_top
    | r1_orders_2(X0_52,X1_50,X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5463,c_5462])).

cnf(c_8685,plain,
    ( k10_lattice3(sK9,sK12,sK12) = sK12
    | sP2(sK9,sK12,sK12) != iProver_top
    | r1_orders_2(sK9,sK12,sK12) != iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8637])).

cnf(c_8221,plain,
    ( k10_lattice3(sK9,X0_50,X1_50) != X2_50
    | sK12 != X2_50
    | sK12 = k10_lattice3(sK9,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_8222,plain,
    ( k10_lattice3(sK9,sK12,sK12) != sK12
    | sK12 = k10_lattice3(sK9,sK12,sK12)
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_8221])).

cnf(c_28,negated_conjecture,
    ( ~ r1_orders_2(sK9,sK10,sK12)
    | r1_orders_2(sK9,sK11,sK13)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4868,negated_conjecture,
    ( ~ r1_orders_2(sK9,sK10,sK12)
    | r1_orders_2(sK9,sK11,sK13)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_5470,plain,
    ( k13_lattice3(sK9,sK10,sK11) != sK12
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK13) = iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4868])).

cnf(c_8148,plain,
    ( k13_lattice3(sK9,sK11,sK10) != sK12
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK13) = iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8106,c_5470])).

cnf(c_29,negated_conjecture,
    ( r1_orders_2(sK9,sK10,sK13)
    | ~ r1_orders_2(sK9,sK10,sK12)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4867,negated_conjecture,
    ( r1_orders_2(sK9,sK10,sK13)
    | ~ r1_orders_2(sK9,sK10,sK12)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_5471,plain,
    ( k13_lattice3(sK9,sK10,sK11) != sK12
    | r1_orders_2(sK9,sK10,sK13) = iProver_top
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4867])).

cnf(c_8147,plain,
    ( k13_lattice3(sK9,sK11,sK10) != sK12
    | r1_orders_2(sK9,sK10,sK13) = iProver_top
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8106,c_5471])).

cnf(c_30,negated_conjecture,
    ( ~ r1_orders_2(sK9,sK10,sK12)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | m1_subset_1(sK13,u1_struct_0(sK9))
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4866,negated_conjecture,
    ( ~ r1_orders_2(sK9,sK10,sK12)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | m1_subset_1(sK13,u1_struct_0(sK9))
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_5472,plain,
    ( k13_lattice3(sK9,sK10,sK11) != sK12
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top
    | m1_subset_1(sK13,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4866])).

cnf(c_8146,plain,
    ( k13_lattice3(sK9,sK11,sK10) != sK12
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top
    | m1_subset_1(sK13,u1_struct_0(sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8106,c_5472])).

cnf(c_27,negated_conjecture,
    ( ~ r1_orders_2(sK9,sK10,sK12)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | ~ r1_orders_2(sK9,sK12,sK13)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4869,negated_conjecture,
    ( ~ r1_orders_2(sK9,sK10,sK12)
    | ~ r1_orders_2(sK9,sK11,sK12)
    | ~ r1_orders_2(sK9,sK12,sK13)
    | k13_lattice3(sK9,sK10,sK11) != sK12 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_5469,plain,
    ( k13_lattice3(sK9,sK10,sK11) != sK12
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top
    | r1_orders_2(sK9,sK12,sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4869])).

cnf(c_8145,plain,
    ( k13_lattice3(sK9,sK11,sK10) != sK12
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top
    | r1_orders_2(sK9,sK12,sK13) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8106,c_5469])).

cnf(c_6536,plain,
    ( k10_lattice3(sK9,sK11,sK10) != X0_50
    | sK12 != X0_50
    | sK12 = k10_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_7694,plain,
    ( k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,X0_50,X1_50)
    | sK12 = k10_lattice3(sK9,sK11,sK10)
    | sK12 != k13_lattice3(sK9,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_6536])).

cnf(c_7699,plain,
    ( k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK12,sK12)
    | sK12 = k10_lattice3(sK9,sK11,sK10)
    | sK12 != k13_lattice3(sK9,sK12,sK12) ),
    inference(instantiation,[status(thm)],[c_7694])).

cnf(c_7518,plain,
    ( k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK10,sK11)
    | sK12 = k10_lattice3(sK9,sK11,sK10)
    | sK12 != k13_lattice3(sK9,sK10,sK11) ),
    inference(instantiation,[status(thm)],[c_6536])).

cnf(c_7495,plain,
    ( ~ sP2(sK9,sK10,sK11)
    | ~ r1_orders_2(sK9,X0_50,sK7(sK9,sK10,sK11,X0_50))
    | ~ r1_orders_2(sK9,sK10,X0_50)
    | ~ r1_orders_2(sK9,sK11,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | k10_lattice3(sK9,sK11,sK10) = X0_50 ),
    inference(instantiation,[status(thm)],[c_4876])).

cnf(c_7511,plain,
    ( k10_lattice3(sK9,sK11,sK10) = X0_50
    | sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,X0_50,sK7(sK9,sK10,sK11,X0_50)) != iProver_top
    | r1_orders_2(sK9,sK10,X0_50) != iProver_top
    | r1_orders_2(sK9,sK11,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7495])).

cnf(c_7513,plain,
    ( k10_lattice3(sK9,sK11,sK10) = sK12
    | sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,sK10,sK12) != iProver_top
    | r1_orders_2(sK9,sK11,sK12) != iProver_top
    | r1_orders_2(sK9,sK12,sK7(sK9,sK10,sK11,sK12)) != iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7511])).

cnf(c_6014,plain,
    ( X0_50 != X1_50
    | k13_lattice3(sK9,sK11,sK10) != X1_50
    | k13_lattice3(sK9,sK11,sK10) = X0_50 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_7484,plain,
    ( X0_50 != k10_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK11,sK10) = X0_50
    | k13_lattice3(sK9,sK11,sK10) != k10_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_6014])).

cnf(c_7485,plain,
    ( k13_lattice3(sK9,sK11,sK10) != k10_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK11,sK10) = sK12
    | sK12 != k10_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_7484])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_792,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_793,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | m1_subset_1(k10_lattice3(sK9,X1,X0),u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_4852,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK9))
    | m1_subset_1(k10_lattice3(sK9,X1_50,X0_50),u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_793])).

cnf(c_7444,plain,
    ( m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4852])).

cnf(c_7445,plain,
    ( m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7444])).

cnf(c_5989,plain,
    ( k13_lattice3(sK9,X0_50,X1_50) != X2_50
    | sK12 != X2_50
    | sK12 = k13_lattice3(sK9,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_7282,plain,
    ( k13_lattice3(sK9,X0_50,X1_50) != k10_lattice3(sK9,X1_50,X0_50)
    | sK12 != k10_lattice3(sK9,X1_50,X0_50)
    | sK12 = k13_lattice3(sK9,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_5989])).

cnf(c_7283,plain,
    ( k13_lattice3(sK9,sK12,sK12) != k10_lattice3(sK9,sK12,sK12)
    | sK12 != k10_lattice3(sK9,sK12,sK12)
    | sK12 = k13_lattice3(sK9,sK12,sK12) ),
    inference(instantiation,[status(thm)],[c_7282])).

cnf(c_6223,plain,
    ( X0_50 != k13_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK11,sK10) = X0_50
    | k13_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_6014])).

cnf(c_7032,plain,
    ( k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK11,sK10) = k10_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_6223])).

cnf(c_19,plain,
    ( ~ sP2(X0,X1,X2)
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4871,plain,
    ( ~ sP2(X0_52,X0_50,X1_50)
    | r1_orders_2(X0_52,X0_50,k10_lattice3(X0_52,X1_50,X0_50))
    | ~ m1_subset_1(k10_lattice3(X0_52,X1_50,X0_50),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_5467,plain,
    ( sP2(X0_52,X0_50,X1_50) != iProver_top
    | r1_orders_2(X0_52,X0_50,k10_lattice3(X0_52,X1_50,X0_50)) = iProver_top
    | m1_subset_1(k10_lattice3(X0_52,X1_50,X0_50),u1_struct_0(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4871])).

cnf(c_6924,plain,
    ( sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,sK10,k10_lattice3(sK9,sK11,sK10)) = iProver_top
    | m1_subset_1(k13_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6398,c_5467])).

cnf(c_6928,plain,
    ( sP2(sK9,sK10,sK11) != iProver_top
    | r1_orders_2(sK9,sK10,k13_lattice3(sK9,sK11,sK10)) = iProver_top
    | m1_subset_1(k13_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6924,c_6398])).

cnf(c_4891,plain,
    ( ~ m1_subset_1(X0_50,X0_51)
    | m1_subset_1(X1_50,X0_51)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_5873,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK9))
    | ~ m1_subset_1(k10_lattice3(sK9,X1_50,X2_50),u1_struct_0(sK9))
    | X0_50 != k10_lattice3(sK9,X1_50,X2_50) ),
    inference(instantiation,[status(thm)],[c_4891])).

cnf(c_6491,plain,
    ( ~ m1_subset_1(k10_lattice3(sK9,X0_50,X1_50),u1_struct_0(sK9))
    | m1_subset_1(k13_lattice3(sK9,sK10,sK11),u1_struct_0(sK9))
    | k13_lattice3(sK9,sK10,sK11) != k10_lattice3(sK9,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_5873])).

cnf(c_6852,plain,
    ( ~ m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9))
    | m1_subset_1(k13_lattice3(sK9,sK10,sK11),u1_struct_0(sK9))
    | k13_lattice3(sK9,sK10,sK11) != k10_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_6491])).

cnf(c_6853,plain,
    ( k13_lattice3(sK9,sK10,sK11) != k10_lattice3(sK9,sK11,sK10)
    | m1_subset_1(k10_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k13_lattice3(sK9,sK10,sK11),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6852])).

cnf(c_5918,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | m1_subset_1(X1_50,u1_struct_0(sK9))
    | X1_50 != X0_50 ),
    inference(instantiation,[status(thm)],[c_4891])).

cnf(c_6483,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK9))
    | m1_subset_1(k13_lattice3(sK9,sK11,sK10),u1_struct_0(sK9))
    | k13_lattice3(sK9,sK11,sK10) != X0_50 ),
    inference(instantiation,[status(thm)],[c_5918])).

cnf(c_6841,plain,
    ( ~ m1_subset_1(k13_lattice3(sK9,sK10,sK11),u1_struct_0(sK9))
    | m1_subset_1(k13_lattice3(sK9,sK11,sK10),u1_struct_0(sK9))
    | k13_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK10,sK11) ),
    inference(instantiation,[status(thm)],[c_6483])).

cnf(c_6842,plain,
    ( k13_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK10,sK11)
    | m1_subset_1(k13_lattice3(sK9,sK10,sK11),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k13_lattice3(sK9,sK11,sK10),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6841])).

cnf(c_6105,plain,
    ( X0_50 != X1_50
    | X0_50 = k13_lattice3(sK9,sK10,sK11)
    | k13_lattice3(sK9,sK10,sK11) != X1_50 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_6357,plain,
    ( X0_50 = k13_lattice3(sK9,sK10,sK11)
    | X0_50 != k13_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK10,sK11) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_6105])).

cnf(c_6767,plain,
    ( k10_lattice3(sK9,sK11,sK10) = k13_lattice3(sK9,sK10,sK11)
    | k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK10,sK11) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_6357])).

cnf(c_6208,plain,
    ( X0_50 != X1_50
    | k13_lattice3(sK9,X2_50,X3_50) != X1_50
    | k13_lattice3(sK9,X2_50,X3_50) = X0_50 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_6420,plain,
    ( X0_50 != k13_lattice3(sK9,X1_50,X2_50)
    | k13_lattice3(sK9,X2_50,X1_50) = X0_50
    | k13_lattice3(sK9,X2_50,X1_50) != k13_lattice3(sK9,X1_50,X2_50) ),
    inference(instantiation,[status(thm)],[c_6208])).

cnf(c_6595,plain,
    ( k10_lattice3(sK9,X0_50,X1_50) != k13_lattice3(sK9,X0_50,X1_50)
    | k13_lattice3(sK9,X1_50,X0_50) = k10_lattice3(sK9,X0_50,X1_50)
    | k13_lattice3(sK9,X1_50,X0_50) != k13_lattice3(sK9,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_6420])).

cnf(c_6596,plain,
    ( k10_lattice3(sK9,sK12,sK12) != k13_lattice3(sK9,sK12,sK12)
    | k13_lattice3(sK9,sK12,sK12) = k10_lattice3(sK9,sK12,sK12)
    | k13_lattice3(sK9,sK12,sK12) != k13_lattice3(sK9,sK12,sK12) ),
    inference(instantiation,[status(thm)],[c_6595])).

cnf(c_4888,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_6382,plain,
    ( sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_4888])).

cnf(c_6224,plain,
    ( k13_lattice3(sK9,sK11,sK10) = k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_4888])).

cnf(c_6048,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | k10_lattice3(sK9,sK11,sK10) = k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_4858])).

cnf(c_5913,plain,
    ( X0_50 != X1_50
    | k13_lattice3(sK9,sK10,sK11) != X1_50
    | k13_lattice3(sK9,sK10,sK11) = X0_50 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_5987,plain,
    ( X0_50 != k13_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK10,sK11) = X0_50
    | k13_lattice3(sK9,sK10,sK11) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_5913])).

cnf(c_6047,plain,
    ( k10_lattice3(sK9,sK11,sK10) != k13_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK10,sK11) = k10_lattice3(sK9,sK11,sK10)
    | k13_lattice3(sK9,sK10,sK11) != k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_5987])).

cnf(c_6010,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | k13_lattice3(sK9,sK11,sK10) = k13_lattice3(sK9,sK10,sK11) ),
    inference(instantiation,[status(thm)],[c_4857])).

cnf(c_5974,plain,
    ( sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_4888])).

cnf(c_5944,plain,
    ( k13_lattice3(sK9,sK10,sK11) != X0_50
    | sK12 != X0_50
    | sK12 = k13_lattice3(sK9,sK10,sK11) ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_5945,plain,
    ( k13_lattice3(sK9,sK10,sK11) != sK12
    | sK12 = k13_lattice3(sK9,sK10,sK11)
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_5944])).

cnf(c_5924,plain,
    ( sK13 = sK13 ),
    inference(instantiation,[status(thm)],[c_4888])).

cnf(c_5908,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK11,u1_struct_0(sK9))
    | k13_lattice3(sK9,sK10,sK11) = k13_lattice3(sK9,sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_4857])).

cnf(c_4945,plain,
    ( ~ m1_subset_1(sK12,u1_struct_0(sK9))
    | k10_lattice3(sK9,sK12,sK12) = k13_lattice3(sK9,sK12,sK12) ),
    inference(instantiation,[status(thm)],[c_4858])).

cnf(c_4939,plain,
    ( k13_lattice3(sK9,sK10,sK11) = sK12
    | r1_orders_2(sK9,sK10,sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4863])).

cnf(c_4897,plain,
    ( sK12 = sK12 ),
    inference(instantiation,[status(thm)],[c_4888])).

cnf(c_4890,plain,
    ( X0_50 != X1_50
    | X2_50 != X3_50
    | k13_lattice3(X0_52,X0_50,X2_50) = k13_lattice3(X0_52,X1_50,X3_50) ),
    theory(equality)).

cnf(c_4893,plain,
    ( k13_lattice3(sK9,sK12,sK12) = k13_lattice3(sK9,sK12,sK12)
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_4890])).

cnf(c_2,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_119,plain,
    ( sP1(X0) != iProver_top
    | sP0(X0) = iProver_top
    | v1_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_121,plain,
    ( sP1(sK9) != iProver_top
    | sP0(sK9) = iProver_top
    | v1_lattice3(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_13,plain,
    ( sP1(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_88,plain,
    ( sP1(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_90,plain,
    ( sP1(sK9) = iProver_top
    | l1_orders_2(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_44,plain,
    ( m1_subset_1(sK11,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_42,plain,
    ( l1_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( v1_lattice3(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_128100,c_118606,c_118273,c_112692,c_93099,c_76478,c_55414,c_32444,c_32431,c_32427,c_32425,c_27156,c_26681,c_17832,c_17830,c_17243,c_17025,c_14717,c_12464,c_12462,c_10348,c_9588,c_9203,c_8685,c_8222,c_8148,c_8147,c_8146,c_8145,c_7699,c_7518,c_7513,c_7485,c_7445,c_7283,c_7032,c_6928,c_6853,c_6842,c_6767,c_6596,c_6382,c_6224,c_6048,c_6047,c_6010,c_5974,c_5945,c_5924,c_5908,c_4945,c_4939,c_4938,c_4897,c_4893,c_121,c_90,c_45,c_34,c_44,c_35,c_43,c_36,c_42,c_41])).


%------------------------------------------------------------------------------
