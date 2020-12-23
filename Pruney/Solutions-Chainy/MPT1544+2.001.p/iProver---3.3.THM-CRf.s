%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:29 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  211 (27598 expanded)
%              Number of clauses        :  159 (5414 expanded)
%              Number of leaves         :   11 (9057 expanded)
%              Depth                    :   29
%              Number of atoms          : 1405 (438524 expanded)
%              Number of equality atoms :  373 (48913 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK5)
        & r1_orders_2(X0,X2,sK5)
        & r1_orders_2(X0,X1,sK5)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
              ( ~ r1_orders_2(X0,sK4,X4)
              & r1_orders_2(X0,X2,X4)
              & r1_orders_2(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X2,sK4)
          | ~ r1_orders_2(X0,X1,sK4)
          | k13_lattice3(X0,X1,X2) != sK4 )
        & ( ( ! [X5] :
                ( r1_orders_2(X0,sK4,X5)
                | ~ r1_orders_2(X0,X2,X5)
                | ~ r1_orders_2(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_orders_2(X0,X2,sK4)
            & r1_orders_2(X0,X1,sK4) )
          | k13_lattice3(X0,X1,X2) = sK4 )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
                  & r1_orders_2(X0,sK3,X4)
                  & r1_orders_2(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK3,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | k13_lattice3(X0,X1,sK3) != X3 )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X3,X5)
                    | ~ r1_orders_2(X0,sK3,X5)
                    | ~ r1_orders_2(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,sK3,X3)
                & r1_orders_2(X0,X1,X3) )
              | k13_lattice3(X0,X1,sK3) = X3 )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
                      & r1_orders_2(X0,sK2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,sK2,X3)
                  | k13_lattice3(X0,sK2,X2) != X3 )
                & ( ( ! [X5] :
                        ( r1_orders_2(X0,X3,X5)
                        | ~ r1_orders_2(X0,X2,X5)
                        | ~ r1_orders_2(X0,sK2,X5)
                        | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,sK2,X3) )
                  | k13_lattice3(X0,sK2,X2) = X3 )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
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
                        ( ~ r1_orders_2(sK1,X3,X4)
                        & r1_orders_2(sK1,X2,X4)
                        & r1_orders_2(sK1,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(sK1)) )
                    | ~ r1_orders_2(sK1,X2,X3)
                    | ~ r1_orders_2(sK1,X1,X3)
                    | k13_lattice3(sK1,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(sK1,X3,X5)
                          | ~ r1_orders_2(sK1,X2,X5)
                          | ~ r1_orders_2(sK1,X1,X5)
                          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                      & r1_orders_2(sK1,X2,X3)
                      & r1_orders_2(sK1,X1,X3) )
                    | k13_lattice3(sK1,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ( ~ r1_orders_2(sK1,sK4,sK5)
        & r1_orders_2(sK1,sK3,sK5)
        & r1_orders_2(sK1,sK2,sK5)
        & m1_subset_1(sK5,u1_struct_0(sK1)) )
      | ~ r1_orders_2(sK1,sK3,sK4)
      | ~ r1_orders_2(sK1,sK2,sK4)
      | k13_lattice3(sK1,sK2,sK3) != sK4 )
    & ( ( ! [X5] :
            ( r1_orders_2(sK1,sK4,X5)
            | ~ r1_orders_2(sK1,sK3,X5)
            | ~ r1_orders_2(sK1,sK2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & r1_orders_2(sK1,sK3,sK4)
        & r1_orders_2(sK1,sK2,sK4) )
      | k13_lattice3(sK1,sK2,sK3) = sK4 )
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f26,f25,f24,f23,f22])).

fof(f41,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
                        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,
    ( r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X5] :
      ( r1_orders_2(sK1,sK4,X5)
      | ~ r1_orders_2(sK1,sK3,X5)
      | ~ r1_orders_2(sK1,sK2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | k13_lattice3(sK1,sK2,sK3) = sK4 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f46,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,
    ( r1_orders_2(sK1,sK2,sK5)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f31,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f48,plain,
    ( r1_orders_2(sK1,sK3,sK5)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,
    ( ~ r1_orders_2(sK1,sK4,sK5)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_671,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_995,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_670,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_996,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k13_lattice3(sK1,X1,X0) = k10_lattice3(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k13_lattice3(sK1,X1,X0) = k10_lattice3(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_21,c_19])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | k13_lattice3(sK1,X1_43,X0_43) = k10_lattice3(sK1,X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_473])).

cnf(c_1004,plain,
    ( k13_lattice3(sK1,X0_43,X1_43) = k10_lattice3(sK1,X0_43,X1_43)
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_1672,plain,
    ( k13_lattice3(sK1,sK2,X0_43) = k10_lattice3(sK1,sK2,X0_43)
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_996,c_1004])).

cnf(c_1843,plain,
    ( k13_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_995,c_1672])).

cnf(c_14,negated_conjecture,
    ( r1_orders_2(sK1,sK3,sK4)
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_674,negated_conjecture,
    ( r1_orders_2(sK1,sK3,sK4)
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_992,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1872,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1843,c_992])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_152,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_0])).

cnf(c_153,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_296,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_20])).

cnf(c_297,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_301,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_297,c_21,c_19])).

cnf(c_302,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_301])).

cnf(c_668,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X2_43,X1_43)
    | r1_orders_2(sK1,X2_43,sK0(sK1,X0_43,X2_43,X1_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_43,X2_43) = X1_43 ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_998,plain,
    ( k10_lattice3(sK1,X0_43,X1_43) = X2_43
    | r1_orders_2(sK1,X0_43,X2_43) != iProver_top
    | r1_orders_2(sK1,X1_43,X2_43) != iProver_top
    | r1_orders_2(sK1,X1_43,sK0(sK1,X0_43,X1_43,X2_43)) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_157,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_0])).

cnf(c_158,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_157])).

cnf(c_263,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_158,c_20])).

cnf(c_264,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_268,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_21,c_19])).

cnf(c_269,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_669,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X2_43,X1_43)
    | ~ r1_orders_2(sK1,X1_43,sK0(sK1,X0_43,X2_43,X1_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_43,X2_43) = X1_43 ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_997,plain,
    ( k10_lattice3(sK1,X0_43,X1_43) = X2_43
    | r1_orders_2(sK1,X0_43,X2_43) != iProver_top
    | r1_orders_2(sK1,X1_43,X2_43) != iProver_top
    | r1_orders_2(sK1,X2_43,sK0(sK1,X0_43,X1_43,X2_43)) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_2694,plain,
    ( k10_lattice3(sK1,X0_43,X1_43) = X1_43
    | r1_orders_2(sK1,X0_43,X1_43) != iProver_top
    | r1_orders_2(sK1,X1_43,X1_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_997])).

cnf(c_3000,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | k10_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK4,sK4) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_2694])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_673,negated_conjecture,
    ( r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_993,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_13,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,X0)
    | ~ r1_orders_2(sK1,sK3,X0)
    | r1_orders_2(sK1,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_675,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,X0_43)
    | ~ r1_orders_2(sK1,sK3,X0_43)
    | r1_orders_2(sK1,sK4,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_991,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK2,X0_43) != iProver_top
    | r1_orders_2(sK1,sK3,X0_43) != iProver_top
    | r1_orders_2(sK1,sK4,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_1545,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | r1_orders_2(sK1,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_991])).

cnf(c_698,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1660,plain,
    ( r1_orders_2(sK1,sK4,sK4) = iProver_top
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1545,c_27,c_698])).

cnf(c_1661,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1660])).

cnf(c_1869,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1843,c_1661])).

cnf(c_3133,plain,
    ( k10_lattice3(sK1,sK3,sK4) = sK4
    | k10_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3000,c_26,c_27,c_1869])).

cnf(c_3134,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | k10_lattice3(sK1,sK3,sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_3133])).

cnf(c_7,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_119,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_0])).

cnf(c_120,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_119])).

cnf(c_448,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_120,c_20])).

cnf(c_449,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_451,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_21,c_19])).

cnf(c_663,plain,
    ( r1_orders_2(sK1,X0_43,k10_lattice3(sK1,X0_43,X1_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_1003,plain,
    ( r1_orders_2(sK1,X0_43,k10_lattice3(sK1,X0_43,X1_43)) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_3138,plain,
    ( k10_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1003])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0_43,X0_44)
    | m1_subset_1(X1_43,X0_44)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_1305,plain,
    ( m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | X0_43 != sK4 ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_1371,plain,
    ( m1_subset_1(k10_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_43,X1_43) != sK4 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1828,plain,
    ( m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_1829,plain,
    ( k10_lattice3(sK1,sK2,sK3) != sK4
    | m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1828])).

cnf(c_2066,plain,
    ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_2067,plain,
    ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) = iProver_top
    | m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2066])).

cnf(c_1870,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK2,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1843,c_993])).

cnf(c_12,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | m1_subset_1(sK5,u1_struct_0(sK1))
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_676,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | m1_subset_1(sK5,u1_struct_0(sK1))
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_990,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_1874,plain,
    ( k10_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1843,c_990])).

cnf(c_3143,plain,
    ( k10_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1874])).

cnf(c_1280,plain,
    ( ~ r1_orders_2(sK1,X0_43,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | ~ r1_orders_2(sK1,sK4,sK0(sK1,sK2,X0_43,sK4))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,X0_43) = sK4 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1488,plain,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK3,sK4))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_1489,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK3,sK4)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_145,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_0])).

cnf(c_146,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_329,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_146,c_20])).

cnf(c_330,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_332,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_21,c_19])).

cnf(c_333,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_667,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X2_43,X1_43)
    | r1_orders_2(sK1,X0_43,sK0(sK1,X0_43,X2_43,X1_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_43,X2_43) = X1_43 ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_999,plain,
    ( k10_lattice3(sK1,X0_43,X1_43) = X2_43
    | r1_orders_2(sK1,X0_43,X2_43) != iProver_top
    | r1_orders_2(sK1,X1_43,X2_43) != iProver_top
    | r1_orders_2(sK1,X0_43,sK0(sK1,X0_43,X1_43,X2_43)) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_1871,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK2,X0_43) != iProver_top
    | r1_orders_2(sK1,sK3,X0_43) != iProver_top
    | r1_orders_2(sK1,sK4,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1843,c_991])).

cnf(c_2824,plain,
    ( k10_lattice3(sK1,sK2,X0_43) = X1_43
    | k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,X0_43,X1_43) != iProver_top
    | r1_orders_2(sK1,sK2,X1_43) != iProver_top
    | r1_orders_2(sK1,sK3,sK0(sK1,sK2,X0_43,X1_43)) != iProver_top
    | r1_orders_2(sK1,sK4,sK0(sK1,sK2,X0_43,X1_43)) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_1871])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_138,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_0])).

cnf(c_139,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_138])).

cnf(c_358,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_139,c_20])).

cnf(c_359,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_21,c_19])).

cnf(c_364,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_666,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X2_43,X1_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0_43,X2_43,X1_43),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_43,X2_43) = X1_43 ),
    inference(subtyping,[status(esa)],[c_364])).

cnf(c_1780,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,sK2,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,X0_43) = X1_43 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1784,plain,
    ( k10_lattice3(sK1,sK2,X0_43) = X1_43
    | r1_orders_2(sK1,X0_43,X1_43) != iProver_top
    | r1_orders_2(sK1,sK2,X1_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_3415,plain,
    ( k10_lattice3(sK1,sK2,X0_43) = X1_43
    | k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,X0_43,X1_43) != iProver_top
    | r1_orders_2(sK1,sK2,X1_43) != iProver_top
    | r1_orders_2(sK1,sK3,sK0(sK1,sK2,X0_43,X1_43)) != iProver_top
    | r1_orders_2(sK1,sK4,sK0(sK1,sK2,X0_43,X1_43)) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2824,c_25,c_1784])).

cnf(c_3429,plain,
    ( k10_lattice3(sK1,sK2,sK3) = X0_43
    | k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK2,X0_43) != iProver_top
    | r1_orders_2(sK1,sK3,X0_43) != iProver_top
    | r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK3,X0_43)) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_3415])).

cnf(c_3431,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3429])).

cnf(c_3434,plain,
    ( r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3143,c_25,c_26,c_27,c_1489,c_1870,c_1872,c_1874,c_3431])).

cnf(c_3441,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1870,c_3434])).

cnf(c_3591,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3441,c_25,c_26,c_27,c_1489,c_1870,c_1872,c_3431])).

cnf(c_3751,plain,
    ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3138,c_25,c_26,c_27,c_1489,c_1829,c_1870,c_1872,c_2067,c_3431])).

cnf(c_3755,plain,
    ( r1_orders_2(sK1,sK2,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3751,c_3591])).

cnf(c_11,negated_conjecture,
    ( r1_orders_2(sK1,sK2,sK5)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_677,negated_conjecture,
    ( r1_orders_2(sK1,sK2,sK5)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_989,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK2,sK5) = iProver_top
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_1875,plain,
    ( k10_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK2,sK5) = iProver_top
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1843,c_989])).

cnf(c_3142,plain,
    ( k10_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK2,sK5) = iProver_top
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1875])).

cnf(c_3759,plain,
    ( k10_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK2,sK5) = iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3755,c_3142])).

cnf(c_693,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK2,sK5) = iProver_top
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_3600,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_3591,c_1843])).

cnf(c_3629,plain,
    ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_1003])).

cnf(c_3650,plain,
    ( r1_orders_2(sK1,sK2,sK4) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3629,c_3591])).

cnf(c_6,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_126,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_0])).

cnf(c_127,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_126])).

cnf(c_424,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_127,c_20])).

cnf(c_425,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X1,X0),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_429,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_21,c_19])).

cnf(c_664,plain,
    ( r1_orders_2(sK1,X0_43,k10_lattice3(sK1,X1_43,X0_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X1_43,X0_43),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_1002,plain,
    ( r1_orders_2(sK1,X0_43,k10_lattice3(sK1,X1_43,X0_43)) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_lattice3(sK1,X1_43,X0_43),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_3628,plain,
    ( r1_orders_2(sK1,sK3,k10_lattice3(sK1,sK2,sK3)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_1002])).

cnf(c_3659,plain,
    ( r1_orders_2(sK1,sK3,sK4) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3628,c_3591])).

cnf(c_4863,plain,
    ( r1_orders_2(sK1,sK2,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3759,c_25,c_26,c_27,c_1489,c_1870,c_1872,c_1875,c_3431,c_3650,c_3659])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_131,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_0])).

cnf(c_132,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_131])).

cnf(c_391,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_132,c_20])).

cnf(c_392,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_21,c_19])).

cnf(c_397,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_396])).

cnf(c_665,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X2_43,X1_43)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0_43,X2_43),X1_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0_43,X2_43),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_397])).

cnf(c_1001,plain,
    ( r1_orders_2(sK1,X0_43,X1_43) != iProver_top
    | r1_orders_2(sK1,X2_43,X1_43) != iProver_top
    | r1_orders_2(sK1,k10_lattice3(sK1,X0_43,X2_43),X1_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_lattice3(sK1,X0_43,X2_43),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_3139,plain,
    ( k10_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43) = iProver_top
    | r1_orders_2(sK1,sK2,X0_43) != iProver_top
    | r1_orders_2(sK1,sK3,X0_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1001])).

cnf(c_1781,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | r1_orders_2(sK1,k10_lattice3(sK1,sK2,X0_43),X1_43)
    | ~ r1_orders_2(sK1,sK2,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,X0_43),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_3848,plain,
    ( r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43)
    | ~ r1_orders_2(sK1,sK2,X0_43)
    | ~ r1_orders_2(sK1,sK3,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1781])).

cnf(c_3849,plain,
    ( r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43) = iProver_top
    | r1_orders_2(sK1,sK2,X0_43) != iProver_top
    | r1_orders_2(sK1,sK3,X0_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3848])).

cnf(c_4304,plain,
    ( m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK1,sK3,X0_43) != iProver_top
    | r1_orders_2(sK1,sK2,X0_43) != iProver_top
    | r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3139,c_25,c_26,c_27,c_1489,c_1829,c_1870,c_1872,c_3431,c_3849])).

cnf(c_4305,plain,
    ( r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43) = iProver_top
    | r1_orders_2(sK1,sK2,X0_43) != iProver_top
    | r1_orders_2(sK1,sK3,X0_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4304])).

cnf(c_4310,plain,
    ( r1_orders_2(sK1,sK2,X0_43) != iProver_top
    | r1_orders_2(sK1,sK3,X0_43) != iProver_top
    | r1_orders_2(sK1,sK4,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4305,c_3591])).

cnf(c_4869,plain,
    ( r1_orders_2(sK1,sK3,sK5) != iProver_top
    | r1_orders_2(sK1,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4863,c_4310])).

cnf(c_694,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_10,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | r1_orders_2(sK1,sK3,sK5)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_678,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | r1_orders_2(sK1,sK3,sK5)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_692,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK5) = iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_9,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK4,sK5)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_679,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK4,sK5)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_691,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK2,sK4) != iProver_top
    | r1_orders_2(sK1,sK3,sK4) != iProver_top
    | r1_orders_2(sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4869,c_3659,c_3650,c_3600,c_694,c_692,c_691,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n015.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 11:05:23 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.31  % Running in FOF mode
% 2.99/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/0.96  
% 2.99/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.96  
% 2.99/0.96  ------  iProver source info
% 2.99/0.96  
% 2.99/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.96  git: non_committed_changes: false
% 2.99/0.96  git: last_make_outside_of_git: false
% 2.99/0.96  
% 2.99/0.96  ------ 
% 2.99/0.96  
% 2.99/0.96  ------ Input Options
% 2.99/0.96  
% 2.99/0.96  --out_options                           all
% 2.99/0.96  --tptp_safe_out                         true
% 2.99/0.96  --problem_path                          ""
% 2.99/0.96  --include_path                          ""
% 2.99/0.96  --clausifier                            res/vclausify_rel
% 2.99/0.96  --clausifier_options                    --mode clausify
% 2.99/0.96  --stdin                                 false
% 2.99/0.96  --stats_out                             all
% 2.99/0.96  
% 2.99/0.96  ------ General Options
% 2.99/0.96  
% 2.99/0.96  --fof                                   false
% 2.99/0.96  --time_out_real                         305.
% 2.99/0.96  --time_out_virtual                      -1.
% 2.99/0.96  --symbol_type_check                     false
% 2.99/0.96  --clausify_out                          false
% 2.99/0.96  --sig_cnt_out                           false
% 2.99/0.96  --trig_cnt_out                          false
% 2.99/0.96  --trig_cnt_out_tolerance                1.
% 2.99/0.96  --trig_cnt_out_sk_spl                   false
% 2.99/0.96  --abstr_cl_out                          false
% 2.99/0.96  
% 2.99/0.96  ------ Global Options
% 2.99/0.96  
% 2.99/0.96  --schedule                              default
% 2.99/0.96  --add_important_lit                     false
% 2.99/0.96  --prop_solver_per_cl                    1000
% 2.99/0.96  --min_unsat_core                        false
% 2.99/0.96  --soft_assumptions                      false
% 2.99/0.96  --soft_lemma_size                       3
% 2.99/0.96  --prop_impl_unit_size                   0
% 2.99/0.96  --prop_impl_unit                        []
% 2.99/0.96  --share_sel_clauses                     true
% 2.99/0.96  --reset_solvers                         false
% 2.99/0.96  --bc_imp_inh                            [conj_cone]
% 2.99/0.96  --conj_cone_tolerance                   3.
% 2.99/0.96  --extra_neg_conj                        none
% 2.99/0.96  --large_theory_mode                     true
% 2.99/0.96  --prolific_symb_bound                   200
% 2.99/0.96  --lt_threshold                          2000
% 2.99/0.96  --clause_weak_htbl                      true
% 2.99/0.96  --gc_record_bc_elim                     false
% 2.99/0.96  
% 2.99/0.96  ------ Preprocessing Options
% 2.99/0.96  
% 2.99/0.96  --preprocessing_flag                    true
% 2.99/0.96  --time_out_prep_mult                    0.1
% 2.99/0.96  --splitting_mode                        input
% 2.99/0.96  --splitting_grd                         true
% 2.99/0.96  --splitting_cvd                         false
% 2.99/0.96  --splitting_cvd_svl                     false
% 2.99/0.96  --splitting_nvd                         32
% 2.99/0.96  --sub_typing                            true
% 2.99/0.96  --prep_gs_sim                           true
% 2.99/0.96  --prep_unflatten                        true
% 2.99/0.96  --prep_res_sim                          true
% 2.99/0.96  --prep_upred                            true
% 2.99/0.96  --prep_sem_filter                       exhaustive
% 2.99/0.96  --prep_sem_filter_out                   false
% 2.99/0.96  --pred_elim                             true
% 2.99/0.96  --res_sim_input                         true
% 2.99/0.96  --eq_ax_congr_red                       true
% 2.99/0.96  --pure_diseq_elim                       true
% 2.99/0.96  --brand_transform                       false
% 2.99/0.96  --non_eq_to_eq                          false
% 2.99/0.96  --prep_def_merge                        true
% 2.99/0.96  --prep_def_merge_prop_impl              false
% 2.99/0.96  --prep_def_merge_mbd                    true
% 2.99/0.96  --prep_def_merge_tr_red                 false
% 2.99/0.96  --prep_def_merge_tr_cl                  false
% 2.99/0.96  --smt_preprocessing                     true
% 2.99/0.96  --smt_ac_axioms                         fast
% 2.99/0.96  --preprocessed_out                      false
% 2.99/0.96  --preprocessed_stats                    false
% 2.99/0.96  
% 2.99/0.96  ------ Abstraction refinement Options
% 2.99/0.96  
% 2.99/0.96  --abstr_ref                             []
% 2.99/0.96  --abstr_ref_prep                        false
% 2.99/0.96  --abstr_ref_until_sat                   false
% 2.99/0.96  --abstr_ref_sig_restrict                funpre
% 2.99/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.96  --abstr_ref_under                       []
% 2.99/0.96  
% 2.99/0.96  ------ SAT Options
% 2.99/0.96  
% 2.99/0.96  --sat_mode                              false
% 2.99/0.96  --sat_fm_restart_options                ""
% 2.99/0.96  --sat_gr_def                            false
% 2.99/0.96  --sat_epr_types                         true
% 2.99/0.96  --sat_non_cyclic_types                  false
% 2.99/0.96  --sat_finite_models                     false
% 2.99/0.96  --sat_fm_lemmas                         false
% 2.99/0.96  --sat_fm_prep                           false
% 2.99/0.96  --sat_fm_uc_incr                        true
% 2.99/0.96  --sat_out_model                         small
% 2.99/0.96  --sat_out_clauses                       false
% 2.99/0.96  
% 2.99/0.96  ------ QBF Options
% 2.99/0.96  
% 2.99/0.96  --qbf_mode                              false
% 2.99/0.96  --qbf_elim_univ                         false
% 2.99/0.96  --qbf_dom_inst                          none
% 2.99/0.96  --qbf_dom_pre_inst                      false
% 2.99/0.96  --qbf_sk_in                             false
% 2.99/0.96  --qbf_pred_elim                         true
% 2.99/0.96  --qbf_split                             512
% 2.99/0.96  
% 2.99/0.96  ------ BMC1 Options
% 2.99/0.96  
% 2.99/0.96  --bmc1_incremental                      false
% 2.99/0.96  --bmc1_axioms                           reachable_all
% 2.99/0.96  --bmc1_min_bound                        0
% 2.99/0.96  --bmc1_max_bound                        -1
% 2.99/0.96  --bmc1_max_bound_default                -1
% 2.99/0.96  --bmc1_symbol_reachability              true
% 2.99/0.96  --bmc1_property_lemmas                  false
% 2.99/0.96  --bmc1_k_induction                      false
% 2.99/0.96  --bmc1_non_equiv_states                 false
% 2.99/0.96  --bmc1_deadlock                         false
% 2.99/0.96  --bmc1_ucm                              false
% 2.99/0.96  --bmc1_add_unsat_core                   none
% 2.99/0.96  --bmc1_unsat_core_children              false
% 2.99/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.96  --bmc1_out_stat                         full
% 2.99/0.96  --bmc1_ground_init                      false
% 2.99/0.96  --bmc1_pre_inst_next_state              false
% 2.99/0.96  --bmc1_pre_inst_state                   false
% 2.99/0.96  --bmc1_pre_inst_reach_state             false
% 2.99/0.96  --bmc1_out_unsat_core                   false
% 2.99/0.96  --bmc1_aig_witness_out                  false
% 2.99/0.96  --bmc1_verbose                          false
% 2.99/0.96  --bmc1_dump_clauses_tptp                false
% 2.99/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.96  --bmc1_dump_file                        -
% 2.99/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.96  --bmc1_ucm_extend_mode                  1
% 2.99/0.96  --bmc1_ucm_init_mode                    2
% 2.99/0.96  --bmc1_ucm_cone_mode                    none
% 2.99/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.96  --bmc1_ucm_relax_model                  4
% 2.99/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.96  --bmc1_ucm_layered_model                none
% 2.99/0.96  --bmc1_ucm_max_lemma_size               10
% 2.99/0.96  
% 2.99/0.96  ------ AIG Options
% 2.99/0.96  
% 2.99/0.96  --aig_mode                              false
% 2.99/0.96  
% 2.99/0.96  ------ Instantiation Options
% 2.99/0.96  
% 2.99/0.96  --instantiation_flag                    true
% 2.99/0.96  --inst_sos_flag                         false
% 2.99/0.96  --inst_sos_phase                        true
% 2.99/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.96  --inst_lit_sel_side                     num_symb
% 2.99/0.96  --inst_solver_per_active                1400
% 2.99/0.96  --inst_solver_calls_frac                1.
% 2.99/0.96  --inst_passive_queue_type               priority_queues
% 2.99/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.96  --inst_passive_queues_freq              [25;2]
% 2.99/0.96  --inst_dismatching                      true
% 2.99/0.96  --inst_eager_unprocessed_to_passive     true
% 2.99/0.96  --inst_prop_sim_given                   true
% 2.99/0.96  --inst_prop_sim_new                     false
% 2.99/0.96  --inst_subs_new                         false
% 2.99/0.96  --inst_eq_res_simp                      false
% 2.99/0.96  --inst_subs_given                       false
% 2.99/0.96  --inst_orphan_elimination               true
% 2.99/0.96  --inst_learning_loop_flag               true
% 2.99/0.96  --inst_learning_start                   3000
% 2.99/0.96  --inst_learning_factor                  2
% 2.99/0.96  --inst_start_prop_sim_after_learn       3
% 2.99/0.96  --inst_sel_renew                        solver
% 2.99/0.96  --inst_lit_activity_flag                true
% 2.99/0.96  --inst_restr_to_given                   false
% 2.99/0.96  --inst_activity_threshold               500
% 2.99/0.96  --inst_out_proof                        true
% 2.99/0.96  
% 2.99/0.96  ------ Resolution Options
% 2.99/0.96  
% 2.99/0.96  --resolution_flag                       true
% 2.99/0.96  --res_lit_sel                           adaptive
% 2.99/0.96  --res_lit_sel_side                      none
% 2.99/0.96  --res_ordering                          kbo
% 2.99/0.96  --res_to_prop_solver                    active
% 2.99/0.96  --res_prop_simpl_new                    false
% 2.99/0.96  --res_prop_simpl_given                  true
% 2.99/0.96  --res_passive_queue_type                priority_queues
% 2.99/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.96  --res_passive_queues_freq               [15;5]
% 2.99/0.96  --res_forward_subs                      full
% 2.99/0.96  --res_backward_subs                     full
% 2.99/0.96  --res_forward_subs_resolution           true
% 2.99/0.96  --res_backward_subs_resolution          true
% 2.99/0.96  --res_orphan_elimination                true
% 2.99/0.96  --res_time_limit                        2.
% 2.99/0.96  --res_out_proof                         true
% 2.99/0.96  
% 2.99/0.96  ------ Superposition Options
% 2.99/0.96  
% 2.99/0.96  --superposition_flag                    true
% 2.99/0.96  --sup_passive_queue_type                priority_queues
% 2.99/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.96  --demod_completeness_check              fast
% 2.99/0.96  --demod_use_ground                      true
% 2.99/0.96  --sup_to_prop_solver                    passive
% 2.99/0.96  --sup_prop_simpl_new                    true
% 2.99/0.96  --sup_prop_simpl_given                  true
% 2.99/0.96  --sup_fun_splitting                     false
% 2.99/0.96  --sup_smt_interval                      50000
% 2.99/0.96  
% 2.99/0.96  ------ Superposition Simplification Setup
% 2.99/0.96  
% 2.99/0.96  --sup_indices_passive                   []
% 2.99/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.96  --sup_full_bw                           [BwDemod]
% 2.99/0.96  --sup_immed_triv                        [TrivRules]
% 2.99/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.96  --sup_immed_bw_main                     []
% 2.99/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.96  
% 2.99/0.96  ------ Combination Options
% 2.99/0.96  
% 2.99/0.96  --comb_res_mult                         3
% 2.99/0.96  --comb_sup_mult                         2
% 2.99/0.96  --comb_inst_mult                        10
% 2.99/0.96  
% 2.99/0.96  ------ Debug Options
% 2.99/0.96  
% 2.99/0.96  --dbg_backtrace                         false
% 2.99/0.96  --dbg_dump_prop_clauses                 false
% 2.99/0.96  --dbg_dump_prop_clauses_file            -
% 2.99/0.96  --dbg_out_stat                          false
% 2.99/0.96  ------ Parsing...
% 2.99/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.96  
% 2.99/0.96  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.99/0.96  
% 2.99/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.96  
% 2.99/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.96  ------ Proving...
% 2.99/0.96  ------ Problem Properties 
% 2.99/0.96  
% 2.99/0.96  
% 2.99/0.96  clauses                                 18
% 2.99/0.96  conjectures                             10
% 2.99/0.96  EPR                                     0
% 2.99/0.96  Horn                                    12
% 2.99/0.96  unary                                   3
% 2.99/0.96  binary                                  2
% 2.99/0.96  lits                                    74
% 2.99/0.96  lits eq                                 12
% 2.99/0.96  fd_pure                                 0
% 2.99/0.96  fd_pseudo                               0
% 2.99/0.96  fd_cond                                 0
% 2.99/0.96  fd_pseudo_cond                          4
% 2.99/0.96  AC symbols                              0
% 2.99/0.96  
% 2.99/0.96  ------ Schedule dynamic 5 is on 
% 2.99/0.96  
% 2.99/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.96  
% 2.99/0.96  
% 2.99/0.96  ------ 
% 2.99/0.96  Current options:
% 2.99/0.96  ------ 
% 2.99/0.96  
% 2.99/0.96  ------ Input Options
% 2.99/0.96  
% 2.99/0.96  --out_options                           all
% 2.99/0.96  --tptp_safe_out                         true
% 2.99/0.96  --problem_path                          ""
% 2.99/0.96  --include_path                          ""
% 2.99/0.96  --clausifier                            res/vclausify_rel
% 2.99/0.96  --clausifier_options                    --mode clausify
% 2.99/0.96  --stdin                                 false
% 2.99/0.96  --stats_out                             all
% 2.99/0.96  
% 2.99/0.96  ------ General Options
% 2.99/0.96  
% 2.99/0.96  --fof                                   false
% 2.99/0.96  --time_out_real                         305.
% 2.99/0.96  --time_out_virtual                      -1.
% 2.99/0.96  --symbol_type_check                     false
% 2.99/0.96  --clausify_out                          false
% 2.99/0.96  --sig_cnt_out                           false
% 2.99/0.96  --trig_cnt_out                          false
% 2.99/0.96  --trig_cnt_out_tolerance                1.
% 2.99/0.96  --trig_cnt_out_sk_spl                   false
% 2.99/0.96  --abstr_cl_out                          false
% 2.99/0.96  
% 2.99/0.96  ------ Global Options
% 2.99/0.96  
% 2.99/0.96  --schedule                              default
% 2.99/0.96  --add_important_lit                     false
% 2.99/0.96  --prop_solver_per_cl                    1000
% 2.99/0.96  --min_unsat_core                        false
% 2.99/0.96  --soft_assumptions                      false
% 2.99/0.96  --soft_lemma_size                       3
% 2.99/0.96  --prop_impl_unit_size                   0
% 2.99/0.96  --prop_impl_unit                        []
% 2.99/0.96  --share_sel_clauses                     true
% 2.99/0.96  --reset_solvers                         false
% 2.99/0.96  --bc_imp_inh                            [conj_cone]
% 2.99/0.96  --conj_cone_tolerance                   3.
% 2.99/0.96  --extra_neg_conj                        none
% 2.99/0.96  --large_theory_mode                     true
% 2.99/0.96  --prolific_symb_bound                   200
% 2.99/0.96  --lt_threshold                          2000
% 2.99/0.96  --clause_weak_htbl                      true
% 2.99/0.96  --gc_record_bc_elim                     false
% 2.99/0.96  
% 2.99/0.96  ------ Preprocessing Options
% 2.99/0.96  
% 2.99/0.96  --preprocessing_flag                    true
% 2.99/0.96  --time_out_prep_mult                    0.1
% 2.99/0.96  --splitting_mode                        input
% 2.99/0.96  --splitting_grd                         true
% 2.99/0.96  --splitting_cvd                         false
% 2.99/0.96  --splitting_cvd_svl                     false
% 2.99/0.96  --splitting_nvd                         32
% 2.99/0.96  --sub_typing                            true
% 2.99/0.96  --prep_gs_sim                           true
% 2.99/0.96  --prep_unflatten                        true
% 2.99/0.96  --prep_res_sim                          true
% 2.99/0.96  --prep_upred                            true
% 2.99/0.96  --prep_sem_filter                       exhaustive
% 2.99/0.96  --prep_sem_filter_out                   false
% 2.99/0.96  --pred_elim                             true
% 2.99/0.96  --res_sim_input                         true
% 2.99/0.96  --eq_ax_congr_red                       true
% 2.99/0.96  --pure_diseq_elim                       true
% 2.99/0.96  --brand_transform                       false
% 2.99/0.96  --non_eq_to_eq                          false
% 2.99/0.96  --prep_def_merge                        true
% 2.99/0.96  --prep_def_merge_prop_impl              false
% 2.99/0.96  --prep_def_merge_mbd                    true
% 2.99/0.96  --prep_def_merge_tr_red                 false
% 2.99/0.96  --prep_def_merge_tr_cl                  false
% 2.99/0.96  --smt_preprocessing                     true
% 2.99/0.96  --smt_ac_axioms                         fast
% 2.99/0.96  --preprocessed_out                      false
% 2.99/0.96  --preprocessed_stats                    false
% 2.99/0.96  
% 2.99/0.96  ------ Abstraction refinement Options
% 2.99/0.96  
% 2.99/0.96  --abstr_ref                             []
% 2.99/0.96  --abstr_ref_prep                        false
% 2.99/0.96  --abstr_ref_until_sat                   false
% 2.99/0.96  --abstr_ref_sig_restrict                funpre
% 2.99/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.96  --abstr_ref_under                       []
% 2.99/0.96  
% 2.99/0.96  ------ SAT Options
% 2.99/0.96  
% 2.99/0.96  --sat_mode                              false
% 2.99/0.96  --sat_fm_restart_options                ""
% 2.99/0.96  --sat_gr_def                            false
% 2.99/0.96  --sat_epr_types                         true
% 2.99/0.96  --sat_non_cyclic_types                  false
% 2.99/0.96  --sat_finite_models                     false
% 2.99/0.96  --sat_fm_lemmas                         false
% 2.99/0.96  --sat_fm_prep                           false
% 2.99/0.96  --sat_fm_uc_incr                        true
% 2.99/0.96  --sat_out_model                         small
% 2.99/0.96  --sat_out_clauses                       false
% 2.99/0.96  
% 2.99/0.96  ------ QBF Options
% 2.99/0.96  
% 2.99/0.96  --qbf_mode                              false
% 2.99/0.96  --qbf_elim_univ                         false
% 2.99/0.96  --qbf_dom_inst                          none
% 2.99/0.96  --qbf_dom_pre_inst                      false
% 2.99/0.96  --qbf_sk_in                             false
% 2.99/0.96  --qbf_pred_elim                         true
% 2.99/0.96  --qbf_split                             512
% 2.99/0.96  
% 2.99/0.96  ------ BMC1 Options
% 2.99/0.96  
% 2.99/0.96  --bmc1_incremental                      false
% 2.99/0.96  --bmc1_axioms                           reachable_all
% 2.99/0.96  --bmc1_min_bound                        0
% 2.99/0.96  --bmc1_max_bound                        -1
% 2.99/0.96  --bmc1_max_bound_default                -1
% 2.99/0.96  --bmc1_symbol_reachability              true
% 2.99/0.96  --bmc1_property_lemmas                  false
% 2.99/0.96  --bmc1_k_induction                      false
% 2.99/0.96  --bmc1_non_equiv_states                 false
% 2.99/0.96  --bmc1_deadlock                         false
% 2.99/0.96  --bmc1_ucm                              false
% 2.99/0.96  --bmc1_add_unsat_core                   none
% 2.99/0.96  --bmc1_unsat_core_children              false
% 2.99/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.96  --bmc1_out_stat                         full
% 2.99/0.96  --bmc1_ground_init                      false
% 2.99/0.96  --bmc1_pre_inst_next_state              false
% 2.99/0.96  --bmc1_pre_inst_state                   false
% 2.99/0.96  --bmc1_pre_inst_reach_state             false
% 2.99/0.96  --bmc1_out_unsat_core                   false
% 2.99/0.96  --bmc1_aig_witness_out                  false
% 2.99/0.96  --bmc1_verbose                          false
% 2.99/0.96  --bmc1_dump_clauses_tptp                false
% 2.99/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.96  --bmc1_dump_file                        -
% 2.99/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.96  --bmc1_ucm_extend_mode                  1
% 2.99/0.96  --bmc1_ucm_init_mode                    2
% 2.99/0.96  --bmc1_ucm_cone_mode                    none
% 2.99/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.96  --bmc1_ucm_relax_model                  4
% 2.99/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.96  --bmc1_ucm_layered_model                none
% 2.99/0.96  --bmc1_ucm_max_lemma_size               10
% 2.99/0.96  
% 2.99/0.96  ------ AIG Options
% 2.99/0.96  
% 2.99/0.96  --aig_mode                              false
% 2.99/0.96  
% 2.99/0.96  ------ Instantiation Options
% 2.99/0.96  
% 2.99/0.96  --instantiation_flag                    true
% 2.99/0.96  --inst_sos_flag                         false
% 2.99/0.96  --inst_sos_phase                        true
% 2.99/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.96  --inst_lit_sel_side                     none
% 2.99/0.96  --inst_solver_per_active                1400
% 2.99/0.96  --inst_solver_calls_frac                1.
% 2.99/0.96  --inst_passive_queue_type               priority_queues
% 2.99/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.96  --inst_passive_queues_freq              [25;2]
% 2.99/0.96  --inst_dismatching                      true
% 2.99/0.96  --inst_eager_unprocessed_to_passive     true
% 2.99/0.96  --inst_prop_sim_given                   true
% 2.99/0.96  --inst_prop_sim_new                     false
% 2.99/0.96  --inst_subs_new                         false
% 2.99/0.96  --inst_eq_res_simp                      false
% 2.99/0.96  --inst_subs_given                       false
% 2.99/0.96  --inst_orphan_elimination               true
% 2.99/0.96  --inst_learning_loop_flag               true
% 2.99/0.96  --inst_learning_start                   3000
% 2.99/0.96  --inst_learning_factor                  2
% 2.99/0.96  --inst_start_prop_sim_after_learn       3
% 2.99/0.96  --inst_sel_renew                        solver
% 2.99/0.96  --inst_lit_activity_flag                true
% 2.99/0.96  --inst_restr_to_given                   false
% 2.99/0.96  --inst_activity_threshold               500
% 2.99/0.96  --inst_out_proof                        true
% 2.99/0.96  
% 2.99/0.96  ------ Resolution Options
% 2.99/0.96  
% 2.99/0.96  --resolution_flag                       false
% 2.99/0.96  --res_lit_sel                           adaptive
% 2.99/0.96  --res_lit_sel_side                      none
% 2.99/0.96  --res_ordering                          kbo
% 2.99/0.96  --res_to_prop_solver                    active
% 2.99/0.96  --res_prop_simpl_new                    false
% 2.99/0.96  --res_prop_simpl_given                  true
% 2.99/0.96  --res_passive_queue_type                priority_queues
% 2.99/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.96  --res_passive_queues_freq               [15;5]
% 2.99/0.96  --res_forward_subs                      full
% 2.99/0.96  --res_backward_subs                     full
% 2.99/0.96  --res_forward_subs_resolution           true
% 2.99/0.96  --res_backward_subs_resolution          true
% 2.99/0.96  --res_orphan_elimination                true
% 2.99/0.96  --res_time_limit                        2.
% 2.99/0.96  --res_out_proof                         true
% 2.99/0.96  
% 2.99/0.96  ------ Superposition Options
% 2.99/0.96  
% 2.99/0.96  --superposition_flag                    true
% 2.99/0.96  --sup_passive_queue_type                priority_queues
% 2.99/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.96  --demod_completeness_check              fast
% 2.99/0.96  --demod_use_ground                      true
% 2.99/0.96  --sup_to_prop_solver                    passive
% 2.99/0.96  --sup_prop_simpl_new                    true
% 2.99/0.96  --sup_prop_simpl_given                  true
% 2.99/0.96  --sup_fun_splitting                     false
% 2.99/0.96  --sup_smt_interval                      50000
% 2.99/0.96  
% 2.99/0.96  ------ Superposition Simplification Setup
% 2.99/0.96  
% 2.99/0.96  --sup_indices_passive                   []
% 2.99/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.96  --sup_full_bw                           [BwDemod]
% 2.99/0.96  --sup_immed_triv                        [TrivRules]
% 2.99/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.96  --sup_immed_bw_main                     []
% 2.99/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.96  
% 2.99/0.96  ------ Combination Options
% 2.99/0.96  
% 2.99/0.96  --comb_res_mult                         3
% 2.99/0.96  --comb_sup_mult                         2
% 2.99/0.96  --comb_inst_mult                        10
% 2.99/0.96  
% 2.99/0.96  ------ Debug Options
% 2.99/0.96  
% 2.99/0.96  --dbg_backtrace                         false
% 2.99/0.96  --dbg_dump_prop_clauses                 false
% 2.99/0.96  --dbg_dump_prop_clauses_file            -
% 2.99/0.96  --dbg_out_stat                          false
% 2.99/0.96  
% 2.99/0.96  
% 2.99/0.96  
% 2.99/0.96  
% 2.99/0.96  ------ Proving...
% 2.99/0.96  
% 2.99/0.96  
% 2.99/0.96  % SZS status Theorem for theBenchmark.p
% 2.99/0.96  
% 2.99/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.96  
% 2.99/0.96  fof(f4,conjecture,(
% 2.99/0.96    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.99/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.96  
% 2.99/0.96  fof(f5,negated_conjecture,(
% 2.99/0.96    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.99/0.96    inference(negated_conjecture,[],[f4])).
% 2.99/0.96  
% 2.99/0.96  fof(f12,plain,(
% 2.99/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k13_lattice3(X0,X1,X2) = X3 <~> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)))),
% 2.99/0.96    inference(ennf_transformation,[],[f5])).
% 2.99/0.96  
% 2.99/0.96  fof(f13,plain,(
% 2.99/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k13_lattice3(X0,X1,X2) = X3 <~> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0))),
% 2.99/0.96    inference(flattening,[],[f12])).
% 2.99/0.96  
% 2.99/0.96  fof(f19,plain,(
% 2.99/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) = X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0))),
% 2.99/0.96    inference(nnf_transformation,[],[f13])).
% 2.99/0.96  
% 2.99/0.96  fof(f20,plain,(
% 2.99/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0))),
% 2.99/0.96    inference(flattening,[],[f19])).
% 2.99/0.96  
% 2.99/0.96  fof(f21,plain,(
% 2.99/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0))),
% 2.99/0.96    inference(rectify,[],[f20])).
% 2.99/0.96  
% 2.99/0.96  fof(f26,plain,(
% 2.99/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK5) & r1_orders_2(X0,X2,sK5) & r1_orders_2(X0,X1,sK5) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.99/0.96    introduced(choice_axiom,[])).
% 2.99/0.96  
% 2.99/0.96  fof(f25,plain,(
% 2.99/0.96    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_orders_2(X0,sK4,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,sK4) | ~r1_orders_2(X0,X1,sK4) | k13_lattice3(X0,X1,X2) != sK4) & ((! [X5] : (r1_orders_2(X0,sK4,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,sK4) & r1_orders_2(X0,X1,sK4)) | k13_lattice3(X0,X1,X2) = sK4) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.99/0.96    introduced(choice_axiom,[])).
% 2.99/0.96  
% 2.99/0.96  fof(f24,plain,(
% 2.99/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : ((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,sK3,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,sK3,X3) | ~r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,sK3) != X3) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,sK3,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,sK3,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,sK3) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.99/0.96    introduced(choice_axiom,[])).
% 2.99/0.96  
% 2.99/0.96  fof(f23,plain,(
% 2.99/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,sK2,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,sK2,X3) | k13_lattice3(X0,sK2,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,sK2,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,sK2,X3)) | k13_lattice3(X0,sK2,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.99/0.96    introduced(choice_axiom,[])).
% 2.99/0.96  
% 2.99/0.96  fof(f22,plain,(
% 2.99/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(sK1,X3,X4) & r1_orders_2(sK1,X2,X4) & r1_orders_2(sK1,X1,X4) & m1_subset_1(X4,u1_struct_0(sK1))) | ~r1_orders_2(sK1,X2,X3) | ~r1_orders_2(sK1,X1,X3) | k13_lattice3(sK1,X1,X2) != X3) & ((! [X5] : (r1_orders_2(sK1,X3,X5) | ~r1_orders_2(sK1,X2,X5) | ~r1_orders_2(sK1,X1,X5) | ~m1_subset_1(X5,u1_struct_0(sK1))) & r1_orders_2(sK1,X2,X3) & r1_orders_2(sK1,X1,X3)) | k13_lattice3(sK1,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1))),
% 2.99/0.96    introduced(choice_axiom,[])).
% 2.99/0.96  
% 2.99/0.96  fof(f27,plain,(
% 2.99/0.96    (((((~r1_orders_2(sK1,sK4,sK5) & r1_orders_2(sK1,sK3,sK5) & r1_orders_2(sK1,sK2,sK5) & m1_subset_1(sK5,u1_struct_0(sK1))) | ~r1_orders_2(sK1,sK3,sK4) | ~r1_orders_2(sK1,sK2,sK4) | k13_lattice3(sK1,sK2,sK3) != sK4) & ((! [X5] : (r1_orders_2(sK1,sK4,X5) | ~r1_orders_2(sK1,sK3,X5) | ~r1_orders_2(sK1,sK2,X5) | ~m1_subset_1(X5,u1_struct_0(sK1))) & r1_orders_2(sK1,sK3,sK4) & r1_orders_2(sK1,sK2,sK4)) | k13_lattice3(sK1,sK2,sK3) = sK4) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1)),
% 2.99/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f26,f25,f24,f23,f22])).
% 2.99/0.96  
% 2.99/0.96  fof(f41,plain,(
% 2.99/0.96    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f40,plain,(
% 2.99/0.96    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f3,axiom,(
% 2.99/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 2.99/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.96  
% 2.99/0.96  fof(f10,plain,(
% 2.99/0.96    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.99/0.96    inference(ennf_transformation,[],[f3])).
% 2.99/0.96  
% 2.99/0.96  fof(f11,plain,(
% 2.99/0.96    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.99/0.96    inference(flattening,[],[f10])).
% 2.99/0.96  
% 2.99/0.96  fof(f36,plain,(
% 2.99/0.96    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f11])).
% 2.99/0.96  
% 2.99/0.96  fof(f38,plain,(
% 2.99/0.96    v1_lattice3(sK1)),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f37,plain,(
% 2.99/0.96    v5_orders_2(sK1)),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f39,plain,(
% 2.99/0.96    l1_orders_2(sK1)),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f44,plain,(
% 2.99/0.96    r1_orders_2(sK1,sK3,sK4) | k13_lattice3(sK1,sK2,sK3) = sK4),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f2,axiom,(
% 2.99/0.96    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.99/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.96  
% 2.99/0.96  fof(f8,plain,(
% 2.99/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.99/0.96    inference(ennf_transformation,[],[f2])).
% 2.99/0.96  
% 2.99/0.96  fof(f9,plain,(
% 2.99/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.99/0.96    inference(flattening,[],[f8])).
% 2.99/0.96  
% 2.99/0.96  fof(f14,plain,(
% 2.99/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.99/0.96    inference(nnf_transformation,[],[f9])).
% 2.99/0.96  
% 2.99/0.96  fof(f15,plain,(
% 2.99/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.99/0.96    inference(flattening,[],[f14])).
% 2.99/0.96  
% 2.99/0.96  fof(f16,plain,(
% 2.99/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.99/0.96    inference(rectify,[],[f15])).
% 2.99/0.96  
% 2.99/0.96  fof(f17,plain,(
% 2.99/0.96    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.99/0.96    introduced(choice_axiom,[])).
% 2.99/0.96  
% 2.99/0.96  fof(f18,plain,(
% 2.99/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.99/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 2.99/0.96  
% 2.99/0.96  fof(f34,plain,(
% 2.99/0.96    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f18])).
% 2.99/0.96  
% 2.99/0.96  fof(f1,axiom,(
% 2.99/0.96    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.99/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.96  
% 2.99/0.96  fof(f6,plain,(
% 2.99/0.96    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.99/0.96    inference(ennf_transformation,[],[f1])).
% 2.99/0.96  
% 2.99/0.96  fof(f7,plain,(
% 2.99/0.96    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.99/0.96    inference(flattening,[],[f6])).
% 2.99/0.96  
% 2.99/0.96  fof(f28,plain,(
% 2.99/0.96    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f7])).
% 2.99/0.96  
% 2.99/0.96  fof(f35,plain,(
% 2.99/0.96    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f18])).
% 2.99/0.96  
% 2.99/0.96  fof(f42,plain,(
% 2.99/0.96    m1_subset_1(sK4,u1_struct_0(sK1))),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f43,plain,(
% 2.99/0.96    r1_orders_2(sK1,sK2,sK4) | k13_lattice3(sK1,sK2,sK3) = sK4),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f45,plain,(
% 2.99/0.96    ( ! [X5] : (r1_orders_2(sK1,sK4,X5) | ~r1_orders_2(sK1,sK3,X5) | ~r1_orders_2(sK1,sK2,X5) | ~m1_subset_1(X5,u1_struct_0(sK1)) | k13_lattice3(sK1,sK2,sK3) = sK4) )),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f29,plain,(
% 2.99/0.96    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f18])).
% 2.99/0.96  
% 2.99/0.96  fof(f52,plain,(
% 2.99/0.96    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(equality_resolution,[],[f29])).
% 2.99/0.96  
% 2.99/0.96  fof(f46,plain,(
% 2.99/0.96    m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK3,sK4) | ~r1_orders_2(sK1,sK2,sK4) | k13_lattice3(sK1,sK2,sK3) != sK4),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f33,plain,(
% 2.99/0.96    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f18])).
% 2.99/0.96  
% 2.99/0.96  fof(f32,plain,(
% 2.99/0.96    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f18])).
% 2.99/0.96  
% 2.99/0.96  fof(f47,plain,(
% 2.99/0.96    r1_orders_2(sK1,sK2,sK5) | ~r1_orders_2(sK1,sK3,sK4) | ~r1_orders_2(sK1,sK2,sK4) | k13_lattice3(sK1,sK2,sK3) != sK4),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f30,plain,(
% 2.99/0.96    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f18])).
% 2.99/0.96  
% 2.99/0.96  fof(f51,plain,(
% 2.99/0.96    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(equality_resolution,[],[f30])).
% 2.99/0.96  
% 2.99/0.96  fof(f31,plain,(
% 2.99/0.96    ( ! [X2,X0,X5,X3,X1] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(cnf_transformation,[],[f18])).
% 2.99/0.96  
% 2.99/0.96  fof(f50,plain,(
% 2.99/0.96    ( ! [X2,X0,X5,X1] : (r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.99/0.96    inference(equality_resolution,[],[f31])).
% 2.99/0.96  
% 2.99/0.96  fof(f48,plain,(
% 2.99/0.96    r1_orders_2(sK1,sK3,sK5) | ~r1_orders_2(sK1,sK3,sK4) | ~r1_orders_2(sK1,sK2,sK4) | k13_lattice3(sK1,sK2,sK3) != sK4),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  fof(f49,plain,(
% 2.99/0.96    ~r1_orders_2(sK1,sK4,sK5) | ~r1_orders_2(sK1,sK3,sK4) | ~r1_orders_2(sK1,sK2,sK4) | k13_lattice3(sK1,sK2,sK3) != sK4),
% 2.99/0.96    inference(cnf_transformation,[],[f27])).
% 2.99/0.96  
% 2.99/0.96  cnf(c_17,negated_conjecture,
% 2.99/0.96      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.99/0.96      inference(cnf_transformation,[],[f41]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_671,negated_conjecture,
% 2.99/0.96      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_17]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_995,plain,
% 2.99/0.96      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_18,negated_conjecture,
% 2.99/0.96      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.99/0.96      inference(cnf_transformation,[],[f40]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_670,negated_conjecture,
% 2.99/0.96      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_18]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_996,plain,
% 2.99/0.96      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_8,plain,
% 2.99/0.96      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.99/0.96      | ~ v5_orders_2(X1)
% 2.99/0.96      | ~ l1_orders_2(X1)
% 2.99/0.96      | ~ v1_lattice3(X1)
% 2.99/0.96      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
% 2.99/0.96      inference(cnf_transformation,[],[f36]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_20,negated_conjecture,
% 2.99/0.96      ( v1_lattice3(sK1) ),
% 2.99/0.96      inference(cnf_transformation,[],[f38]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_468,plain,
% 2.99/0.96      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.99/0.96      | ~ v5_orders_2(X1)
% 2.99/0.96      | ~ l1_orders_2(X1)
% 2.99/0.96      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
% 2.99/0.96      | sK1 != X1 ),
% 2.99/0.96      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_469,plain,
% 2.99/0.96      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ v5_orders_2(sK1)
% 2.99/0.96      | ~ l1_orders_2(sK1)
% 2.99/0.96      | k13_lattice3(sK1,X1,X0) = k10_lattice3(sK1,X1,X0) ),
% 2.99/0.96      inference(unflattening,[status(thm)],[c_468]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_21,negated_conjecture,
% 2.99/0.96      ( v5_orders_2(sK1) ),
% 2.99/0.96      inference(cnf_transformation,[],[f37]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_19,negated_conjecture,
% 2.99/0.96      ( l1_orders_2(sK1) ),
% 2.99/0.96      inference(cnf_transformation,[],[f39]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_473,plain,
% 2.99/0.96      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | k13_lattice3(sK1,X1,X0) = k10_lattice3(sK1,X1,X0) ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_469,c_21,c_19]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_662,plain,
% 2.99/0.96      ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | k13_lattice3(sK1,X1_43,X0_43) = k10_lattice3(sK1,X1_43,X0_43) ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_473]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1004,plain,
% 2.99/0.96      ( k13_lattice3(sK1,X0_43,X1_43) = k10_lattice3(sK1,X0_43,X1_43)
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1672,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,X0_43) = k10_lattice3(sK1,sK2,X0_43)
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_996,c_1004]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1843,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK2,sK3) ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_995,c_1672]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_14,negated_conjecture,
% 2.99/0.96      ( r1_orders_2(sK1,sK3,sK4) | k13_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(cnf_transformation,[],[f44]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_674,negated_conjecture,
% 2.99/0.96      ( r1_orders_2(sK1,sK3,sK4) | k13_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_14]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_992,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1872,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) = iProver_top ),
% 2.99/0.96      inference(demodulation,[status(thm)],[c_1843,c_992]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_2,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | v2_struct_0(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(cnf_transformation,[],[f34]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_0,plain,
% 2.99/0.96      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 2.99/0.96      inference(cnf_transformation,[],[f28]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_152,plain,
% 2.99/0.96      ( ~ v1_lattice3(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(global_propositional_subsumption,[status(thm)],[c_2,c_0]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_153,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_152]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_296,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2
% 2.99/0.96      | sK1 != X0 ),
% 2.99/0.96      inference(resolution_lifted,[status(thm)],[c_153,c_20]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_297,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ v5_orders_2(sK1)
% 2.99/0.96      | ~ l1_orders_2(sK1)
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(unflattening,[status(thm)],[c_296]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_301,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_297,c_21,c_19]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_302,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_301]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_668,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2_43,X1_43)
% 2.99/0.96      | r1_orders_2(sK1,X2_43,sK0(sK1,X0_43,X2_43,X1_43))
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0_43,X2_43) = X1_43 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_302]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_998,plain,
% 2.99/0.96      ( k10_lattice3(sK1,X0_43,X1_43) = X2_43
% 2.99/0.96      | r1_orders_2(sK1,X0_43,X2_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,X1_43,X2_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,X1_43,sK0(sK1,X0_43,X1_43,X2_43)) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | v2_struct_0(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(cnf_transformation,[],[f35]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_157,plain,
% 2.99/0.96      ( ~ v1_lattice3(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(global_propositional_subsumption,[status(thm)],[c_1,c_0]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_158,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_157]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_263,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2
% 2.99/0.96      | sK1 != X0 ),
% 2.99/0.96      inference(resolution_lifted,[status(thm)],[c_158,c_20]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_264,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ v5_orders_2(sK1)
% 2.99/0.96      | ~ l1_orders_2(sK1)
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(unflattening,[status(thm)],[c_263]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_268,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_264,c_21,c_19]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_269,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_268]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_669,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2_43,X1_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,X1_43,sK0(sK1,X0_43,X2_43,X1_43))
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0_43,X2_43) = X1_43 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_269]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_997,plain,
% 2.99/0.96      ( k10_lattice3(sK1,X0_43,X1_43) = X2_43
% 2.99/0.96      | r1_orders_2(sK1,X0_43,X2_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,X1_43,X2_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,X2_43,sK0(sK1,X0_43,X1_43,X2_43)) != iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_2694,plain,
% 2.99/0.96      ( k10_lattice3(sK1,X0_43,X1_43) = X1_43
% 2.99/0.96      | r1_orders_2(sK1,X0_43,X1_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,X1_43,X1_43) != iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_998,c_997]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3000,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | k10_lattice3(sK1,sK3,sK4) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK4) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_1872,c_2694]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_26,plain,
% 2.99/0.96      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_16,negated_conjecture,
% 2.99/0.96      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 2.99/0.96      inference(cnf_transformation,[],[f42]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_27,plain,
% 2.99/0.96      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_15,negated_conjecture,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,sK4) | k13_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(cnf_transformation,[],[f43]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_673,negated_conjecture,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,sK4) | k13_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_15]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_993,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_13,negated_conjecture,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,X0)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,X0)
% 2.99/0.96      | r1_orders_2(sK1,sK4,X0)
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(cnf_transformation,[],[f45]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_675,negated_conjecture,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,X0_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,X0_43)
% 2.99/0.96      | r1_orders_2(sK1,sK4,X0_43)
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_13]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_991,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,X0_43) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1545,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK4) = iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_993,c_991]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_698,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1660,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK4,sK4) = iProver_top
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_1545,c_27,c_698]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1661,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK4) = iProver_top ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_1660]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1869,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK4) = iProver_top ),
% 2.99/0.96      inference(demodulation,[status(thm)],[c_1843,c_1661]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3133,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK3,sK4) = sK4
% 2.99/0.96      | k10_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_3000,c_26,c_27,c_1869]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3134,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | k10_lattice3(sK1,sK3,sK4) = sK4 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_3133]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_7,plain,
% 2.99/0.96      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | v2_struct_0(X0) ),
% 2.99/0.96      inference(cnf_transformation,[],[f52]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_119,plain,
% 2.99/0.96      ( ~ v1_lattice3(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
% 2.99/0.96      inference(global_propositional_subsumption,[status(thm)],[c_7,c_0]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_120,plain,
% 2.99/0.96      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0) ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_119]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_448,plain,
% 2.99/0.96      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | sK1 != X0 ),
% 2.99/0.96      inference(resolution_lifted,[status(thm)],[c_120,c_20]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_449,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X0,X1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X0,X1),u1_struct_0(sK1))
% 2.99/0.96      | ~ v5_orders_2(sK1)
% 2.99/0.96      | ~ l1_orders_2(sK1) ),
% 2.99/0.96      inference(unflattening,[status(thm)],[c_448]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_451,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X0,X1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_449,c_21,c_19]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_663,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0_43,k10_lattice3(sK1,X0_43,X1_43))
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_451]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1003,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0_43,k10_lattice3(sK1,X0_43,X1_43)) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(k10_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3138,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK3,sK4) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) = iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_3134,c_1003]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_25,plain,
% 2.99/0.96      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_684,plain,
% 2.99/0.96      ( ~ m1_subset_1(X0_43,X0_44)
% 2.99/0.96      | m1_subset_1(X1_43,X0_44)
% 2.99/0.96      | X1_43 != X0_43 ),
% 2.99/0.96      theory(equality) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1305,plain,
% 2.99/0.96      ( m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 2.99/0.96      | X0_43 != sK4 ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_684]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1371,plain,
% 2.99/0.96      ( m1_subset_1(k10_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0_43,X1_43) != sK4 ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_1305]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1828,plain,
% 2.99/0.96      ( m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_1371]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1829,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) = iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_1828]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_2066,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_663]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_2067,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) = iProver_top
% 2.99/0.96      | m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_2066]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1870,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) = iProver_top ),
% 2.99/0.96      inference(demodulation,[status(thm)],[c_1843,c_993]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_12,negated_conjecture,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1))
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(cnf_transformation,[],[f46]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_676,negated_conjecture,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1))
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_12]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_990,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1874,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(demodulation,[status(thm)],[c_1843,c_990]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3143,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK3,sK4) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_3134,c_1874]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1280,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0_43,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK4,sK0(sK1,sK2,X0_43,sK4))
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,sK2,X0_43) = sK4 ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_669]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1488,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK3,sK4))
% 2.99/0.96      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_1280]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1489,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK3,sK4)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | v2_struct_0(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(cnf_transformation,[],[f33]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_145,plain,
% 2.99/0.96      ( ~ v1_lattice3(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(global_propositional_subsumption,[status(thm)],[c_3,c_0]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_146,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_145]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_329,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2
% 2.99/0.96      | sK1 != X0 ),
% 2.99/0.96      inference(resolution_lifted,[status(thm)],[c_146,c_20]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_330,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ v5_orders_2(sK1)
% 2.99/0.96      | ~ l1_orders_2(sK1)
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(unflattening,[status(thm)],[c_329]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_332,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_330,c_21,c_19]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_333,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_332]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_667,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2_43,X1_43)
% 2.99/0.96      | r1_orders_2(sK1,X0_43,sK0(sK1,X0_43,X2_43,X1_43))
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0_43,X2_43) = X1_43 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_333]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_999,plain,
% 2.99/0.96      ( k10_lattice3(sK1,X0_43,X1_43) = X2_43
% 2.99/0.96      | r1_orders_2(sK1,X0_43,X2_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,X1_43,X2_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,X0_43,sK0(sK1,X0_43,X1_43,X2_43)) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1871,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,X0_43) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(demodulation,[status(thm)],[c_1843,c_991]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_2824,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,X0_43) = X1_43
% 2.99/0.96      | k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,X0_43,X1_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,X1_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK0(sK1,sK2,X0_43,X1_43)) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK0(sK1,sK2,X0_43,X1_43)) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_999,c_1871]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_4,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | v2_struct_0(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(cnf_transformation,[],[f32]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_138,plain,
% 2.99/0.96      ( ~ v1_lattice3(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(global_propositional_subsumption,[status(thm)],[c_4,c_0]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_139,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_138]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_358,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | k10_lattice3(X0,X3,X1) = X2
% 2.99/0.96      | sK1 != X0 ),
% 2.99/0.96      inference(resolution_lifted,[status(thm)],[c_139,c_20]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_359,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
% 2.99/0.96      | ~ v5_orders_2(sK1)
% 2.99/0.96      | ~ l1_orders_2(sK1)
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(unflattening,[status(thm)],[c_358]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_363,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_359,c_21,c_19]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_364,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0,X2) = X1 ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_363]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_666,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2_43,X1_43)
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 2.99/0.96      | m1_subset_1(sK0(sK1,X0_43,X2_43,X1_43),u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,X0_43,X2_43) = X1_43 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_364]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1780,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK2,X1_43)
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.99/0.96      | k10_lattice3(sK1,sK2,X0_43) = X1_43 ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_666]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1784,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,X0_43) = X1_43
% 2.99/0.96      | r1_orders_2(sK1,X0_43,X1_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,X1_43) != iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1)) = iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_1780]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3415,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,X0_43) = X1_43
% 2.99/0.96      | k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,X0_43,X1_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,X1_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK0(sK1,sK2,X0_43,X1_43)) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK0(sK1,sK2,X0_43,X1_43)) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_2824,c_25,c_1784]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3429,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = X0_43
% 2.99/0.96      | k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK3,X0_43)) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_998,c_3415]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3431,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK0(sK1,sK2,sK3,sK4)) = iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_3429]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3434,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_3143,c_25,c_26,c_27,c_1489,c_1870,c_1872,c_1874,
% 2.99/0.96                 c_3431]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3441,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_1870,c_3434]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3591,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_3441,c_25,c_26,c_27,c_1489,c_1870,c_1872,c_3431]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3751,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) = iProver_top ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_3138,c_25,c_26,c_27,c_1489,c_1829,c_1870,c_1872,
% 2.99/0.96                 c_2067,c_3431]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3755,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,sK4) = iProver_top ),
% 2.99/0.96      inference(light_normalisation,[status(thm)],[c_3751,c_3591]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_11,negated_conjecture,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,sK5)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(cnf_transformation,[],[f47]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_677,negated_conjecture,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,sK5)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_11]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_989,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK5) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1875,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK5) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
% 2.99/0.96      inference(demodulation,[status(thm)],[c_1843,c_989]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3142,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK3,sK4) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK5) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_3134,c_1875]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3759,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK3,sK4) = sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK5) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_3755,c_3142]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_693,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK5) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3600,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) = sK4 ),
% 2.99/0.96      inference(demodulation,[status(thm)],[c_3591,c_1843]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3629,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) = iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_3591,c_1003]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3650,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,sK4) = iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(light_normalisation,[status(thm)],[c_3629,c_3591]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_6,plain,
% 2.99/0.96      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | v2_struct_0(X0) ),
% 2.99/0.96      inference(cnf_transformation,[],[f51]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_126,plain,
% 2.99/0.96      ( ~ v1_lattice3(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
% 2.99/0.96      inference(global_propositional_subsumption,[status(thm)],[c_6,c_0]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_127,plain,
% 2.99/0.96      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0) ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_126]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_424,plain,
% 2.99/0.96      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | sK1 != X0 ),
% 2.99/0.96      inference(resolution_lifted,[status(thm)],[c_127,c_20]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_425,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X1,X0))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X1,X0),u1_struct_0(sK1))
% 2.99/0.96      | ~ v5_orders_2(sK1)
% 2.99/0.96      | ~ l1_orders_2(sK1) ),
% 2.99/0.96      inference(unflattening,[status(thm)],[c_424]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_429,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X1,X0))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X1,X0),u1_struct_0(sK1)) ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_425,c_21,c_19]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_664,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0_43,k10_lattice3(sK1,X1_43,X0_43))
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X1_43,X0_43),u1_struct_0(sK1)) ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_429]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1002,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0_43,k10_lattice3(sK1,X1_43,X0_43)) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(k10_lattice3(sK1,X1_43,X0_43),u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3628,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK3,k10_lattice3(sK1,sK2,sK3)) = iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_3591,c_1002]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3659,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK3,sK4) = iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(light_normalisation,[status(thm)],[c_3628,c_3591]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_4863,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,sK5) = iProver_top ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_3759,c_25,c_26,c_27,c_1489,c_1870,c_1872,c_1875,
% 2.99/0.96                 c_3431,c_3650,c_3659]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_5,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0)
% 2.99/0.96      | v2_struct_0(X0) ),
% 2.99/0.96      inference(cnf_transformation,[],[f50]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_131,plain,
% 2.99/0.96      ( ~ v1_lattice3(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X1,X2) ),
% 2.99/0.96      inference(global_propositional_subsumption,[status(thm)],[c_5,c_0]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_132,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | ~ v1_lattice3(X0) ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_131]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_391,plain,
% 2.99/0.96      ( ~ r1_orders_2(X0,X1,X2)
% 2.99/0.96      | ~ r1_orders_2(X0,X3,X2)
% 2.99/0.96      | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
% 2.99/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
% 2.99/0.96      | ~ v5_orders_2(X0)
% 2.99/0.96      | ~ l1_orders_2(X0)
% 2.99/0.96      | sK1 != X0 ),
% 2.99/0.96      inference(resolution_lifted,[status(thm)],[c_132,c_20]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_392,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1))
% 2.99/0.96      | ~ v5_orders_2(sK1)
% 2.99/0.96      | ~ l1_orders_2(sK1) ),
% 2.99/0.96      inference(unflattening,[status(thm)],[c_391]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_396,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1)) ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_392,c_21,c_19]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_397,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0,X1)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2,X1)
% 2.99/0.96      | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
% 2.99/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1)) ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_396]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_665,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,X2_43,X1_43)
% 2.99/0.96      | r1_orders_2(sK1,k10_lattice3(sK1,X0_43,X2_43),X1_43)
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,X0_43,X2_43),u1_struct_0(sK1)) ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_397]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1001,plain,
% 2.99/0.96      ( r1_orders_2(sK1,X0_43,X1_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,X2_43,X1_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,k10_lattice3(sK1,X0_43,X2_43),X1_43) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(k10_lattice3(sK1,X0_43,X2_43),u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3139,plain,
% 2.99/0.96      ( k10_lattice3(sK1,sK3,sK4) = sK4
% 2.99/0.96      | r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,X0_43) != iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_3134,c_1001]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_1781,plain,
% 2.99/0.96      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 2.99/0.96      | r1_orders_2(sK1,k10_lattice3(sK1,sK2,X0_43),X1_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK2,X1_43)
% 2.99/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,sK2,X0_43),u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_665]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3848,plain,
% 2.99/0.96      ( r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK2,X0_43)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,X0_43)
% 2.99/0.96      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.99/0.96      | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.99/0.96      inference(instantiation,[status(thm)],[c_1781]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_3849,plain,
% 2.99/0.96      ( r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,X0_43) != iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_3848]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_4304,plain,
% 2.99/0.96      ( m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43) = iProver_top ),
% 2.99/0.96      inference(global_propositional_subsumption,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_3139,c_25,c_26,c_27,c_1489,c_1829,c_1870,c_1872,
% 2.99/0.96                 c_3431,c_3849]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_4305,plain,
% 2.99/0.96      ( r1_orders_2(sK1,k10_lattice3(sK1,sK2,sK3),X0_43) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK2,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,X0_43) != iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(renaming,[status(thm)],[c_4304]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_4310,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK2,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,X0_43) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,X0_43) = iProver_top
% 2.99/0.96      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(light_normalisation,[status(thm)],[c_4305,c_3591]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_4869,plain,
% 2.99/0.96      ( r1_orders_2(sK1,sK3,sK5) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK5) = iProver_top
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top ),
% 2.99/0.96      inference(superposition,[status(thm)],[c_4863,c_4310]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_694,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_10,negated_conjecture,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK5)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(cnf_transformation,[],[f48]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_678,negated_conjecture,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK5)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_10]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_692,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK5) = iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_9,negated_conjecture,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK4,sK5)
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(cnf_transformation,[],[f49]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_679,negated_conjecture,
% 2.99/0.96      ( ~ r1_orders_2(sK1,sK2,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK3,sK4)
% 2.99/0.96      | ~ r1_orders_2(sK1,sK4,sK5)
% 2.99/0.96      | k13_lattice3(sK1,sK2,sK3) != sK4 ),
% 2.99/0.96      inference(subtyping,[status(esa)],[c_9]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(c_691,plain,
% 2.99/0.96      ( k13_lattice3(sK1,sK2,sK3) != sK4
% 2.99/0.96      | r1_orders_2(sK1,sK2,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK3,sK4) != iProver_top
% 2.99/0.96      | r1_orders_2(sK1,sK4,sK5) != iProver_top ),
% 2.99/0.96      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 2.99/0.96  
% 2.99/0.96  cnf(contradiction,plain,
% 2.99/0.96      ( $false ),
% 2.99/0.96      inference(minisat,
% 2.99/0.96                [status(thm)],
% 2.99/0.96                [c_4869,c_3659,c_3650,c_3600,c_694,c_692,c_691,c_27,c_26,
% 2.99/0.96                 c_25]) ).
% 2.99/0.96  
% 2.99/0.96  
% 2.99/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.96  
% 2.99/0.96  ------                               Statistics
% 2.99/0.96  
% 2.99/0.96  ------ General
% 2.99/0.96  
% 2.99/0.96  abstr_ref_over_cycles:                  0
% 2.99/0.96  abstr_ref_under_cycles:                 0
% 2.99/0.96  gc_basic_clause_elim:                   0
% 2.99/0.96  forced_gc_time:                         0
% 2.99/0.96  parsing_time:                           0.011
% 2.99/0.96  unif_index_cands_time:                  0.
% 2.99/0.96  unif_index_add_time:                    0.
% 2.99/0.96  orderings_time:                         0.
% 2.99/0.96  out_proof_time:                         0.015
% 2.99/0.96  total_time:                             0.189
% 2.99/0.96  num_of_symbols:                         46
% 2.99/0.96  num_of_terms:                           3663
% 2.99/0.96  
% 2.99/0.96  ------ Preprocessing
% 2.99/0.96  
% 2.99/0.96  num_of_splits:                          0
% 2.99/0.96  num_of_split_atoms:                     0
% 2.99/0.96  num_of_reused_defs:                     0
% 2.99/0.96  num_eq_ax_congr_red:                    24
% 2.99/0.96  num_of_sem_filtered_clauses:            2
% 2.99/0.96  num_of_subtypes:                        3
% 2.99/0.96  monotx_restored_types:                  0
% 2.99/0.96  sat_num_of_epr_types:                   0
% 2.99/0.96  sat_num_of_non_cyclic_types:            0
% 2.99/0.96  sat_guarded_non_collapsed_types:        1
% 2.99/0.96  num_pure_diseq_elim:                    0
% 2.99/0.96  simp_replaced_by:                       0
% 2.99/0.96  res_preprocessed:                       87
% 2.99/0.96  prep_upred:                             0
% 2.99/0.96  prep_unflattend:                        8
% 2.99/0.96  smt_new_axioms:                         0
% 2.99/0.96  pred_elim_cands:                        2
% 2.99/0.96  pred_elim:                              3
% 2.99/0.96  pred_elim_cl:                           3
% 2.99/0.96  pred_elim_cycles:                       5
% 2.99/0.96  merged_defs:                            0
% 2.99/0.96  merged_defs_ncl:                        0
% 2.99/0.96  bin_hyper_res:                          0
% 2.99/0.96  prep_cycles:                            4
% 2.99/0.96  pred_elim_time:                         0.007
% 2.99/0.96  splitting_time:                         0.
% 2.99/0.96  sem_filter_time:                        0.
% 2.99/0.96  monotx_time:                            0.
% 2.99/0.96  subtype_inf_time:                       0.001
% 2.99/0.96  
% 2.99/0.96  ------ Problem properties
% 2.99/0.96  
% 2.99/0.96  clauses:                                18
% 2.99/0.96  conjectures:                            10
% 2.99/0.96  epr:                                    0
% 2.99/0.96  horn:                                   12
% 2.99/0.96  ground:                                 9
% 2.99/0.96  unary:                                  3
% 2.99/0.96  binary:                                 2
% 2.99/0.96  lits:                                   74
% 2.99/0.96  lits_eq:                                12
% 2.99/0.96  fd_pure:                                0
% 2.99/0.96  fd_pseudo:                              0
% 2.99/0.96  fd_cond:                                0
% 2.99/0.96  fd_pseudo_cond:                         4
% 2.99/0.96  ac_symbols:                             0
% 2.99/0.96  
% 2.99/0.96  ------ Propositional Solver
% 2.99/0.96  
% 2.99/0.96  prop_solver_calls:                      26
% 2.99/0.96  prop_fast_solver_calls:                 1167
% 2.99/0.96  smt_solver_calls:                       0
% 2.99/0.96  smt_fast_solver_calls:                  0
% 2.99/0.96  prop_num_of_clauses:                    1439
% 2.99/0.96  prop_preprocess_simplified:             3849
% 2.99/0.96  prop_fo_subsumed:                       57
% 2.99/0.96  prop_solver_time:                       0.
% 2.99/0.96  smt_solver_time:                        0.
% 2.99/0.96  smt_fast_solver_time:                   0.
% 2.99/0.96  prop_fast_solver_time:                  0.
% 2.99/0.96  prop_unsat_core_time:                   0.
% 2.99/0.96  
% 2.99/0.96  ------ QBF
% 2.99/0.96  
% 2.99/0.96  qbf_q_res:                              0
% 2.99/0.96  qbf_num_tautologies:                    0
% 2.99/0.96  qbf_prep_cycles:                        0
% 2.99/0.96  
% 2.99/0.96  ------ BMC1
% 2.99/0.96  
% 2.99/0.96  bmc1_current_bound:                     -1
% 2.99/0.96  bmc1_last_solved_bound:                 -1
% 2.99/0.96  bmc1_unsat_core_size:                   -1
% 2.99/0.96  bmc1_unsat_core_parents_size:           -1
% 2.99/0.96  bmc1_merge_next_fun:                    0
% 2.99/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.96  
% 2.99/0.96  ------ Instantiation
% 2.99/0.96  
% 2.99/0.96  inst_num_of_clauses:                    441
% 2.99/0.96  inst_num_in_passive:                    87
% 2.99/0.96  inst_num_in_active:                     258
% 2.99/0.96  inst_num_in_unprocessed:                96
% 2.99/0.96  inst_num_of_loops:                      290
% 2.99/0.96  inst_num_of_learning_restarts:          0
% 2.99/0.96  inst_num_moves_active_passive:          29
% 2.99/0.96  inst_lit_activity:                      0
% 2.99/0.96  inst_lit_activity_moves:                0
% 2.99/0.96  inst_num_tautologies:                   0
% 2.99/0.96  inst_num_prop_implied:                  0
% 2.99/0.96  inst_num_existing_simplified:           0
% 2.99/0.96  inst_num_eq_res_simplified:             0
% 2.99/0.96  inst_num_child_elim:                    0
% 2.99/0.96  inst_num_of_dismatching_blockings:      405
% 2.99/0.96  inst_num_of_non_proper_insts:           476
% 2.99/0.96  inst_num_of_duplicates:                 0
% 2.99/0.96  inst_inst_num_from_inst_to_res:         0
% 2.99/0.96  inst_dismatching_checking_time:         0.
% 2.99/0.96  
% 2.99/0.96  ------ Resolution
% 2.99/0.96  
% 2.99/0.96  res_num_of_clauses:                     0
% 2.99/0.96  res_num_in_passive:                     0
% 2.99/0.96  res_num_in_active:                      0
% 2.99/0.96  res_num_of_loops:                       91
% 2.99/0.96  res_forward_subset_subsumed:            4
% 2.99/0.96  res_backward_subset_subsumed:           0
% 2.99/0.96  res_forward_subsumed:                   0
% 2.99/0.96  res_backward_subsumed:                  0
% 2.99/0.96  res_forward_subsumption_resolution:     0
% 2.99/0.96  res_backward_subsumption_resolution:    0
% 2.99/0.96  res_clause_to_clause_subsumption:       703
% 2.99/0.96  res_orphan_elimination:                 0
% 2.99/0.96  res_tautology_del:                      19
% 2.99/0.96  res_num_eq_res_simplified:              0
% 2.99/0.96  res_num_sel_changes:                    0
% 2.99/0.96  res_moves_from_active_to_pass:          0
% 2.99/0.96  
% 2.99/0.96  ------ Superposition
% 2.99/0.96  
% 2.99/0.96  sup_time_total:                         0.
% 2.99/0.96  sup_time_generating:                    0.
% 2.99/0.96  sup_time_sim_full:                      0.
% 2.99/0.96  sup_time_sim_immed:                     0.
% 2.99/0.96  
% 2.99/0.96  sup_num_of_clauses:                     68
% 2.99/0.96  sup_num_in_active:                      38
% 2.99/0.96  sup_num_in_passive:                     30
% 2.99/0.96  sup_num_of_loops:                       57
% 2.99/0.96  sup_fw_superposition:                   44
% 2.99/0.96  sup_bw_superposition:                   31
% 2.99/0.96  sup_immediate_simplified:               7
% 2.99/0.96  sup_given_eliminated:                   0
% 2.99/0.96  comparisons_done:                       0
% 2.99/0.96  comparisons_avoided:                    8
% 2.99/0.96  
% 2.99/0.96  ------ Simplifications
% 2.99/0.96  
% 2.99/0.96  
% 2.99/0.96  sim_fw_subset_subsumed:                 4
% 2.99/0.96  sim_bw_subset_subsumed:                 13
% 2.99/0.96  sim_fw_subsumed:                        0
% 2.99/0.96  sim_bw_subsumed:                        0
% 2.99/0.96  sim_fw_subsumption_res:                 0
% 2.99/0.96  sim_bw_subsumption_res:                 0
% 2.99/0.96  sim_tautology_del:                      0
% 2.99/0.96  sim_eq_tautology_del:                   2
% 2.99/0.96  sim_eq_res_simp:                        4
% 2.99/0.96  sim_fw_demodulated:                     0
% 2.99/0.96  sim_bw_demodulated:                     15
% 2.99/0.96  sim_light_normalised:                   6
% 2.99/0.96  sim_joinable_taut:                      0
% 2.99/0.96  sim_joinable_simp:                      0
% 2.99/0.96  sim_ac_normalised:                      0
% 2.99/0.96  sim_smt_subsumption:                    0
% 2.99/0.96  
%------------------------------------------------------------------------------
