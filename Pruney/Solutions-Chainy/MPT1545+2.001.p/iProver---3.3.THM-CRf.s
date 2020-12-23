%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:30 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  211 (29073 expanded)
%              Number of clauses        :  159 (5701 expanded)
%              Number of leaves         :   11 (9545 expanded)
%              Depth                    :   29
%              Number of atoms          : 1405 (462017 expanded)
%              Number of equality atoms :  373 (51533 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k12_lattice3(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | k12_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | k12_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | k12_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | k12_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | k12_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(X0,X5,X3)
                          | ~ r1_orders_2(X0,X5,X2)
                          | ~ r1_orders_2(X0,X5,X1)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | k12_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f20])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5,X3)
        & r1_orders_2(X0,sK5,X2)
        & r1_orders_2(X0,sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_orders_2(X0,X4,X2)
                & r1_orders_2(X0,X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X3,X2)
            | ~ r1_orders_2(X0,X3,X1)
            | k12_lattice3(X0,X1,X2) != X3 )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,X3)
                  | ~ r1_orders_2(X0,X5,X2)
                  | ~ r1_orders_2(X0,X5,X1)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_orders_2(X0,X3,X2)
              & r1_orders_2(X0,X3,X1) )
            | k12_lattice3(X0,X1,X2) = X3 )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_orders_2(X0,X4,sK4)
              & r1_orders_2(X0,X4,X2)
              & r1_orders_2(X0,X4,X1)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,sK4,X2)
          | ~ r1_orders_2(X0,sK4,X1)
          | k12_lattice3(X0,X1,X2) != sK4 )
        & ( ( ! [X5] :
                ( r1_orders_2(X0,X5,sK4)
                | ~ r1_orders_2(X0,X5,X2)
                | ~ r1_orders_2(X0,X5,X1)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_orders_2(X0,sK4,X2)
            & r1_orders_2(X0,sK4,X1) )
          | k12_lattice3(X0,X1,X2) = sK4 )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ? [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r1_orders_2(X0,X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,X2)
                | ~ r1_orders_2(X0,X3,X1)
                | k12_lattice3(X0,X1,X2) != X3 )
              & ( ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_orders_2(X0,X5,X2)
                      | ~ r1_orders_2(X0,X5,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X3,X2)
                  & r1_orders_2(X0,X3,X1) )
                | k12_lattice3(X0,X1,X2) = X3 )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,sK3)
                  & r1_orders_2(X0,X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,sK3)
              | ~ r1_orders_2(X0,X3,X1)
              | k12_lattice3(X0,X1,sK3) != X3 )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,sK3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,sK3)
                & r1_orders_2(X0,X3,X1) )
              | k12_lattice3(X0,X1,sK3) = X3 )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | k12_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(X0,X5,X3)
                          | ~ r1_orders_2(X0,X5,X2)
                          | ~ r1_orders_2(X0,X5,X1)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | k12_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,sK2)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,sK2)
                  | k12_lattice3(X0,sK2,X2) != X3 )
                & ( ( ! [X5] :
                        ( r1_orders_2(X0,X5,X3)
                        | ~ r1_orders_2(X0,X5,X2)
                        | ~ r1_orders_2(X0,X5,sK2)
                        | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,sK2) )
                  | k12_lattice3(X0,sK2,X2) = X3 )
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
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1)
                      | k12_lattice3(X0,X1,X2) != X3 )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) = X3 )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(sK1,X4,X3)
                        & r1_orders_2(sK1,X4,X2)
                        & r1_orders_2(sK1,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(sK1)) )
                    | ~ r1_orders_2(sK1,X3,X2)
                    | ~ r1_orders_2(sK1,X3,X1)
                    | k12_lattice3(sK1,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(sK1,X5,X3)
                          | ~ r1_orders_2(sK1,X5,X2)
                          | ~ r1_orders_2(sK1,X5,X1)
                          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                      & r1_orders_2(sK1,X3,X2)
                      & r1_orders_2(sK1,X3,X1) )
                    | k12_lattice3(sK1,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v2_lattice3(sK1)
      & v5_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ( ~ r1_orders_2(sK1,sK5,sK4)
        & r1_orders_2(sK1,sK5,sK3)
        & r1_orders_2(sK1,sK5,sK2)
        & m1_subset_1(sK5,u1_struct_0(sK1)) )
      | ~ r1_orders_2(sK1,sK4,sK3)
      | ~ r1_orders_2(sK1,sK4,sK2)
      | k12_lattice3(sK1,sK2,sK3) != sK4 )
    & ( ( ! [X5] :
            ( r1_orders_2(sK1,X5,sK4)
            | ~ r1_orders_2(sK1,X5,sK3)
            | ~ r1_orders_2(sK1,X5,sK2)
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & r1_orders_2(sK1,sK4,sK3)
        & r1_orders_2(sK1,sK4,sK2) )
      | k12_lattice3(sK1,sK2,sK3) = sK4 )
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v2_lattice3(sK1)
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
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1)
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK0(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK0(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK0(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,
    ( r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X5] :
      ( r1_orders_2(sK1,X5,sK4)
      | ~ r1_orders_2(sK1,X5,sK3)
      | ~ r1_orders_2(sK1,X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | k12_lattice3(sK1,sK2,sK3) = sK4 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f46,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK0(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,
    ( r1_orders_2(sK1,sK5,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f31,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f48,plain,
    ( r1_orders_2(sK1,sK5,sK3)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,
    ( ~ r1_orders_2(sK1,sK5,sK4)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
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
    | ~ v2_lattice3(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
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
    | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_21,c_19])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | k12_lattice3(sK1,X1_43,X0_43) = k11_lattice3(sK1,X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_473])).

cnf(c_1004,plain,
    ( k12_lattice3(sK1,X0_43,X1_43) = k11_lattice3(sK1,X0_43,X1_43)
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_1668,plain,
    ( k12_lattice3(sK1,sK2,X0_43) = k11_lattice3(sK1,sK2,X0_43)
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_996,c_1004])).

cnf(c_1838,plain,
    ( k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_995,c_1668])).

cnf(c_14,negated_conjecture,
    ( r1_orders_2(sK1,sK4,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_674,negated_conjecture,
    ( r1_orders_2(sK1,sK4,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_992,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1867,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_992])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_152,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_0])).

cnf(c_153,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_296,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_20])).

cnf(c_297,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_301,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_297,c_21,c_19])).

cnf(c_302,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_301])).

cnf(c_668,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | r1_orders_2(sK1,sK0(sK1,X1_43,X2_43,X0_43),X2_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1_43,X2_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_998,plain,
    ( k11_lattice3(sK1,X0_43,X1_43) = X2_43
    | r1_orders_2(sK1,X2_43,X0_43) != iProver_top
    | r1_orders_2(sK1,X2_43,X1_43) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0_43,X1_43,X2_43),X1_43) = iProver_top
    | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_157,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_0])).

cnf(c_158,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_157])).

cnf(c_263,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_158,c_20])).

cnf(c_264,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_268,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_21,c_19])).

cnf(c_269,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_669,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | ~ r1_orders_2(sK1,sK0(sK1,X1_43,X2_43,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1_43,X2_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_997,plain,
    ( k11_lattice3(sK1,X0_43,X1_43) = X2_43
    | r1_orders_2(sK1,X2_43,X0_43) != iProver_top
    | r1_orders_2(sK1,X2_43,X1_43) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0_43,X1_43,X2_43),X2_43) != iProver_top
    | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_2689,plain,
    ( k11_lattice3(sK1,X0_43,X1_43) = X1_43
    | r1_orders_2(sK1,X1_43,X0_43) != iProver_top
    | r1_orders_2(sK1,X1_43,X1_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_997])).

cnf(c_2995,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | k11_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK4,sK4) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1867,c_2689])).

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
    ( r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_673,negated_conjecture,
    ( r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_993,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_13,negated_conjecture,
    ( ~ r1_orders_2(sK1,X0,sK2)
    | ~ r1_orders_2(sK1,X0,sK3)
    | r1_orders_2(sK1,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_675,negated_conjecture,
    ( ~ r1_orders_2(sK1,X0_43,sK2)
    | ~ r1_orders_2(sK1,X0_43,sK3)
    | r1_orders_2(sK1,X0_43,sK4)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_991,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,X0_43,sK2) != iProver_top
    | r1_orders_2(sK1,X0_43,sK3) != iProver_top
    | r1_orders_2(sK1,X0_43,sK4) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_1541,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | r1_orders_2(sK1,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_991])).

cnf(c_698,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1656,plain,
    ( r1_orders_2(sK1,sK4,sK4) = iProver_top
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1541,c_27,c_698])).

cnf(c_1657,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1656])).

cnf(c_1864,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_1657])).

cnf(c_3191,plain,
    ( k11_lattice3(sK1,sK3,sK4) = sK4
    | k11_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2995,c_26,c_27,c_1864])).

cnf(c_3192,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | k11_lattice3(sK1,sK3,sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_3191])).

cnf(c_7,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_119,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_0])).

cnf(c_120,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_119])).

cnf(c_448,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_120,c_20])).

cnf(c_449,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_451,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_21,c_19])).

cnf(c_663,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_1003,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_3195,plain,
    ( k11_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_1003])).

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

cnf(c_1370,plain,
    ( m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0_43,X1_43) != sK4 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1823,plain,
    ( m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_1824,plain,
    ( k11_lattice3(sK1,sK2,sK3) != sK4
    | m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1823])).

cnf(c_2062,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2)
    | ~ m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_2063,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2) = iProver_top
    | m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2062])).

cnf(c_1865,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_993])).

cnf(c_12,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | m1_subset_1(sK5,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_676,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | m1_subset_1(sK5,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_990,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_1869,plain,
    ( k11_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_990])).

cnf(c_3201,plain,
    ( k11_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_1869])).

cnf(c_1280,plain,
    ( ~ r1_orders_2(sK1,sK0(sK1,sK2,X0_43,sK4),sK4)
    | ~ r1_orders_2(sK1,sK4,X0_43)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,X0_43) = sK4 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1484,plain,
    ( ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK4),sK4)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_1485,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK4),sK4) != iProver_top
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1484])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_145,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_0])).

cnf(c_146,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_329,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_146,c_20])).

cnf(c_330,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_332,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_21,c_19])).

cnf(c_333,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_667,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | r1_orders_2(sK1,sK0(sK1,X1_43,X2_43,X0_43),X1_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k11_lattice3(sK1,X1_43,X2_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_999,plain,
    ( k11_lattice3(sK1,X0_43,X1_43) = X2_43
    | r1_orders_2(sK1,X2_43,X0_43) != iProver_top
    | r1_orders_2(sK1,X2_43,X1_43) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,X0_43,X1_43,X2_43),X0_43) = iProver_top
    | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_1866,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,X0_43,sK2) != iProver_top
    | r1_orders_2(sK1,X0_43,sK3) != iProver_top
    | r1_orders_2(sK1,X0_43,sK4) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_991])).

cnf(c_2819,plain,
    ( k11_lattice3(sK1,sK2,X0_43) = X1_43
    | k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,X1_43,X0_43) != iProver_top
    | r1_orders_2(sK1,X1_43,sK2) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,sK2,X0_43,X1_43),sK3) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,sK2,X0_43,X1_43),sK4) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_1866])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_138,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK0(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_0])).

cnf(c_139,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_138])).

cnf(c_358,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_139,c_20])).

cnf(c_359,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1,X2,X0),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1,X2,X0),u1_struct_0(sK1))
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_21,c_19])).

cnf(c_364,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1,X2,X0),u1_struct_0(sK1))
    | k11_lattice3(sK1,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_666,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1_43,X2_43,X0_43),u1_struct_0(sK1))
    | k11_lattice3(sK1,X1_43,X2_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_364])).

cnf(c_1775,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,sK2)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,sK2,X1_43,X0_43),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,X1_43) = X0_43 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1779,plain,
    ( k11_lattice3(sK1,sK2,X0_43) = X1_43
    | r1_orders_2(sK1,X1_43,X0_43) != iProver_top
    | r1_orders_2(sK1,X1_43,sK2) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_3473,plain,
    ( k11_lattice3(sK1,sK2,X0_43) = X1_43
    | k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,X1_43,X0_43) != iProver_top
    | r1_orders_2(sK1,X1_43,sK2) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,sK2,X0_43,X1_43),sK3) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,sK2,X0_43,X1_43),sK4) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2819,c_25,c_1779])).

cnf(c_3487,plain,
    ( k11_lattice3(sK1,sK2,sK3) = X0_43
    | k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,X0_43,sK2) != iProver_top
    | r1_orders_2(sK1,X0_43,sK3) != iProver_top
    | r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_43),sK4) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_3473])).

cnf(c_3489,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK4),sK4) = iProver_top
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3487])).

cnf(c_3492,plain,
    ( r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3201,c_25,c_26,c_27,c_1485,c_1865,c_1867,c_1869,c_3489])).

cnf(c_3499,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1865,c_3492])).

cnf(c_3649,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3499,c_25,c_26,c_27,c_1485,c_1865,c_1867,c_3489])).

cnf(c_3799,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3195,c_25,c_26,c_27,c_1485,c_1824,c_1865,c_1867,c_2063,c_3489])).

cnf(c_3803,plain,
    ( r1_orders_2(sK1,sK4,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3799,c_3649])).

cnf(c_11,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | r1_orders_2(sK1,sK5,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_677,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | r1_orders_2(sK1,sK5,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_989,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_1870,plain,
    ( k11_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_989])).

cnf(c_3200,plain,
    ( k11_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_1870])).

cnf(c_3807,plain,
    ( k11_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3803,c_3200])).

cnf(c_693,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_3658,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_3649,c_1838])).

cnf(c_6,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_126,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_0])).

cnf(c_127,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_126])).

cnf(c_424,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_127,c_20])).

cnf(c_425,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_429,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_21,c_19])).

cnf(c_664,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X1_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_1002,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X1_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_3687,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK3) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_1002])).

cnf(c_3708,plain,
    ( r1_orders_2(sK1,sK4,sK3) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3687,c_3649])).

cnf(c_3686,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_1003])).

cnf(c_3717,plain,
    ( r1_orders_2(sK1,sK4,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3686,c_3649])).

cnf(c_4852,plain,
    ( r1_orders_2(sK1,sK5,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3807,c_25,c_26,c_27,c_693,c_3658,c_3708,c_3717])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_131,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_0])).

cnf(c_132,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_131])).

cnf(c_391,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_132,c_20])).

cnf(c_392,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,X0,k11_lattice3(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X1,X2),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,X0,k11_lattice3(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X1,X2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_21,c_19])).

cnf(c_397,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,X0,k11_lattice3(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X1,X2),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_396])).

cnf(c_665,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,X1_43,X2_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X1_43,X2_43),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_397])).

cnf(c_1001,plain,
    ( r1_orders_2(sK1,X0_43,X1_43) != iProver_top
    | r1_orders_2(sK1,X0_43,X2_43) != iProver_top
    | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,X1_43,X2_43)) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k11_lattice3(sK1,X1_43,X2_43),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_3197,plain,
    ( k11_lattice3(sK1,sK3,sK4) = sK4
    | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3)) = iProver_top
    | r1_orders_2(sK1,X0_43,sK2) != iProver_top
    | r1_orders_2(sK1,X0_43,sK3) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_1001])).

cnf(c_1776,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,X1_43))
    | ~ r1_orders_2(sK1,X0_43,sK2)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,sK2,X1_43),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_3934,plain,
    ( r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3))
    | ~ r1_orders_2(sK1,X0_43,sK2)
    | ~ r1_orders_2(sK1,X0_43,sK3)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_3935,plain,
    ( r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3)) = iProver_top
    | r1_orders_2(sK1,X0_43,sK2) != iProver_top
    | r1_orders_2(sK1,X0_43,sK3) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3934])).

cnf(c_4390,plain,
    ( m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK1,X0_43,sK3) != iProver_top
    | r1_orders_2(sK1,X0_43,sK2) != iProver_top
    | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3197,c_25,c_26,c_27,c_1485,c_1824,c_1865,c_1867,c_3489,c_3935])).

cnf(c_4391,plain,
    ( r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3)) = iProver_top
    | r1_orders_2(sK1,X0_43,sK2) != iProver_top
    | r1_orders_2(sK1,X0_43,sK3) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4390])).

cnf(c_4396,plain,
    ( r1_orders_2(sK1,X0_43,sK2) != iProver_top
    | r1_orders_2(sK1,X0_43,sK3) != iProver_top
    | r1_orders_2(sK1,X0_43,sK4) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4391,c_3649])).

cnf(c_4858,plain,
    ( r1_orders_2(sK1,sK5,sK3) != iProver_top
    | r1_orders_2(sK1,sK5,sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4852,c_4396])).

cnf(c_694,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_10,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | r1_orders_2(sK1,sK5,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_678,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | r1_orders_2(sK1,sK5,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_692,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | r1_orders_2(sK1,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_9,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK5,sK4)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_679,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK5,sK4)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_691,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK4
    | r1_orders_2(sK1,sK4,sK2) != iProver_top
    | r1_orders_2(sK1,sK4,sK3) != iProver_top
    | r1_orders_2(sK1,sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4858,c_3717,c_3708,c_3658,c_694,c_692,c_691,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:22:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.27/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/0.99  
% 3.27/0.99  ------  iProver source info
% 3.27/0.99  
% 3.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/0.99  git: non_committed_changes: false
% 3.27/0.99  git: last_make_outside_of_git: false
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     num_symb
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       true
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  ------ Parsing...
% 3.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/0.99  ------ Proving...
% 3.27/0.99  ------ Problem Properties 
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  clauses                                 18
% 3.27/0.99  conjectures                             10
% 3.27/0.99  EPR                                     0
% 3.27/0.99  Horn                                    12
% 3.27/0.99  unary                                   3
% 3.27/0.99  binary                                  2
% 3.27/0.99  lits                                    74
% 3.27/0.99  lits eq                                 12
% 3.27/0.99  fd_pure                                 0
% 3.27/0.99  fd_pseudo                               0
% 3.27/0.99  fd_cond                                 0
% 3.27/0.99  fd_pseudo_cond                          4
% 3.27/0.99  AC symbols                              0
% 3.27/0.99  
% 3.27/0.99  ------ Schedule dynamic 5 is on 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  Current options:
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     none
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       false
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ Proving...
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS status Theorem for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  fof(f4,conjecture,(
% 3.27/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f5,negated_conjecture,(
% 3.27/0.99    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.27/0.99    inference(negated_conjecture,[],[f4])).
% 3.27/0.99  
% 3.27/0.99  fof(f12,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k12_lattice3(X0,X1,X2) = X3 <~> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f5])).
% 3.27/0.99  
% 3.27/0.99  fof(f13,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k12_lattice3(X0,X1,X2) = X3 <~> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0))),
% 3.27/0.99    inference(flattening,[],[f12])).
% 3.27/0.99  
% 3.27/0.99  fof(f19,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) = X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0))),
% 3.27/0.99    inference(nnf_transformation,[],[f13])).
% 3.27/0.99  
% 3.27/0.99  fof(f20,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0))),
% 3.27/0.99    inference(flattening,[],[f19])).
% 3.27/0.99  
% 3.27/0.99  fof(f21,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0))),
% 3.27/0.99    inference(rectify,[],[f20])).
% 3.27/0.99  
% 3.27/0.99  fof(f26,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5,X3) & r1_orders_2(X0,sK5,X2) & r1_orders_2(X0,sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f25,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_orders_2(X0,X4,sK4) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,sK4,X2) | ~r1_orders_2(X0,sK4,X1) | k12_lattice3(X0,X1,X2) != sK4) & ((! [X5] : (r1_orders_2(X0,X5,sK4) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,sK4,X2) & r1_orders_2(X0,sK4,X1)) | k12_lattice3(X0,X1,X2) = sK4) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f24,plain,(
% 3.27/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : ((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,sK3) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,sK3) | ~r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,sK3) != X3) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,sK3) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,sK3) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,sK3) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f23,plain,(
% 3.27/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,sK2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,sK2) | k12_lattice3(X0,sK2,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,sK2) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,sK2)) | k12_lattice3(X0,sK2,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f22,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_orders_2(sK1,X4,X3) & r1_orders_2(sK1,X4,X2) & r1_orders_2(sK1,X4,X1) & m1_subset_1(X4,u1_struct_0(sK1))) | ~r1_orders_2(sK1,X3,X2) | ~r1_orders_2(sK1,X3,X1) | k12_lattice3(sK1,X1,X2) != X3) & ((! [X5] : (r1_orders_2(sK1,X5,X3) | ~r1_orders_2(sK1,X5,X2) | ~r1_orders_2(sK1,X5,X1) | ~m1_subset_1(X5,u1_struct_0(sK1))) & r1_orders_2(sK1,X3,X2) & r1_orders_2(sK1,X3,X1)) | k12_lattice3(sK1,X1,X2) = X3) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v2_lattice3(sK1) & v5_orders_2(sK1))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f27,plain,(
% 3.27/0.99    (((((~r1_orders_2(sK1,sK5,sK4) & r1_orders_2(sK1,sK5,sK3) & r1_orders_2(sK1,sK5,sK2) & m1_subset_1(sK5,u1_struct_0(sK1))) | ~r1_orders_2(sK1,sK4,sK3) | ~r1_orders_2(sK1,sK4,sK2) | k12_lattice3(sK1,sK2,sK3) != sK4) & ((! [X5] : (r1_orders_2(sK1,X5,sK4) | ~r1_orders_2(sK1,X5,sK3) | ~r1_orders_2(sK1,X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK1))) & r1_orders_2(sK1,sK4,sK3) & r1_orders_2(sK1,sK4,sK2)) | k12_lattice3(sK1,sK2,sK3) = sK4) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v2_lattice3(sK1) & v5_orders_2(sK1)),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f26,f25,f24,f23,f22])).
% 3.27/0.99  
% 3.27/0.99  fof(f41,plain,(
% 3.27/0.99    m1_subset_1(sK3,u1_struct_0(sK1))),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f40,plain,(
% 3.27/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f3,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f10,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f3])).
% 3.27/0.99  
% 3.27/0.99  fof(f11,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.27/0.99    inference(flattening,[],[f10])).
% 3.27/0.99  
% 3.27/0.99  fof(f36,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f11])).
% 3.27/0.99  
% 3.27/0.99  fof(f38,plain,(
% 3.27/0.99    v2_lattice3(sK1)),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f37,plain,(
% 3.27/0.99    v5_orders_2(sK1)),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f39,plain,(
% 3.27/0.99    l1_orders_2(sK1)),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f44,plain,(
% 3.27/0.99    r1_orders_2(sK1,sK4,sK3) | k12_lattice3(sK1,sK2,sK3) = sK4),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f2,axiom,(
% 3.27/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f8,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f2])).
% 3.27/0.99  
% 3.27/0.99  fof(f9,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.27/0.99    inference(flattening,[],[f8])).
% 3.27/0.99  
% 3.27/0.99  fof(f14,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.27/0.99    inference(nnf_transformation,[],[f9])).
% 3.27/0.99  
% 3.27/0.99  fof(f15,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.27/0.99    inference(flattening,[],[f14])).
% 3.27/0.99  
% 3.27/0.99  fof(f16,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.27/0.99    inference(rectify,[],[f15])).
% 3.27/0.99  
% 3.27/0.99  fof(f17,plain,(
% 3.27/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f18,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 3.27/0.99  
% 3.27/0.99  fof(f34,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f1,axiom,(
% 3.27/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f6,plain,(
% 3.27/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.27/0.99    inference(ennf_transformation,[],[f1])).
% 3.27/0.99  
% 3.27/0.99  fof(f7,plain,(
% 3.27/0.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 3.27/0.99    inference(flattening,[],[f6])).
% 3.27/0.99  
% 3.27/0.99  fof(f28,plain,(
% 3.27/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f7])).
% 3.27/0.99  
% 3.27/0.99  fof(f35,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f42,plain,(
% 3.27/0.99    m1_subset_1(sK4,u1_struct_0(sK1))),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f43,plain,(
% 3.27/0.99    r1_orders_2(sK1,sK4,sK2) | k12_lattice3(sK1,sK2,sK3) = sK4),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f45,plain,(
% 3.27/0.99    ( ! [X5] : (r1_orders_2(sK1,X5,sK4) | ~r1_orders_2(sK1,X5,sK3) | ~r1_orders_2(sK1,X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK1)) | k12_lattice3(sK1,sK2,sK3) = sK4) )),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f29,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f52,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(equality_resolution,[],[f29])).
% 3.27/0.99  
% 3.27/0.99  fof(f46,plain,(
% 3.27/0.99    m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK4,sK3) | ~r1_orders_2(sK1,sK4,sK2) | k12_lattice3(sK1,sK2,sK3) != sK4),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f33,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f32,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f47,plain,(
% 3.27/0.99    r1_orders_2(sK1,sK5,sK2) | ~r1_orders_2(sK1,sK4,sK3) | ~r1_orders_2(sK1,sK4,sK2) | k12_lattice3(sK1,sK2,sK3) != sK4),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f30,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f51,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(equality_resolution,[],[f30])).
% 3.27/0.99  
% 3.27/0.99  fof(f31,plain,(
% 3.27/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f50,plain,(
% 3.27/0.99    ( ! [X2,X0,X5,X1] : (r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2)) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.27/0.99    inference(equality_resolution,[],[f31])).
% 3.27/0.99  
% 3.27/0.99  fof(f48,plain,(
% 3.27/0.99    r1_orders_2(sK1,sK5,sK3) | ~r1_orders_2(sK1,sK4,sK3) | ~r1_orders_2(sK1,sK4,sK2) | k12_lattice3(sK1,sK2,sK3) != sK4),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f49,plain,(
% 3.27/0.99    ~r1_orders_2(sK1,sK5,sK4) | ~r1_orders_2(sK1,sK4,sK3) | ~r1_orders_2(sK1,sK4,sK2) | k12_lattice3(sK1,sK2,sK3) != sK4),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  cnf(c_17,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_671,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_995,plain,
% 3.27/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_18,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_670,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_996,plain,
% 3.27/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/0.99      | ~ v5_orders_2(X1)
% 3.27/0.99      | ~ l1_orders_2(X1)
% 3.27/0.99      | ~ v2_lattice3(X1)
% 3.27/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_20,negated_conjecture,
% 3.27/0.99      ( v2_lattice3(sK1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_468,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/0.99      | ~ v5_orders_2(X1)
% 3.27/0.99      | ~ l1_orders_2(X1)
% 3.27/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 3.27/0.99      | sK1 != X1 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_469,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | ~ v5_orders_2(sK1)
% 3.27/0.99      | ~ l1_orders_2(sK1)
% 3.27/0.99      | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_468]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_21,negated_conjecture,
% 3.27/0.99      ( v5_orders_2(sK1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_19,negated_conjecture,
% 3.27/0.99      ( l1_orders_2(sK1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_473,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_469,c_21,c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_662,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/0.99      | k12_lattice3(sK1,X1_43,X0_43) = k11_lattice3(sK1,X1_43,X0_43) ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_473]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1004,plain,
% 3.27/0.99      ( k12_lattice3(sK1,X0_43,X1_43) = k11_lattice3(sK1,X0_43,X1_43)
% 3.27/0.99      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1668,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,X0_43) = k11_lattice3(sK1,sK2,X0_43)
% 3.27/0.99      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_996,c_1004]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1838,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_995,c_1668]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_14,negated_conjecture,
% 3.27/0.99      ( r1_orders_2(sK1,sK4,sK3) | k12_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_674,negated_conjecture,
% 3.27/0.99      ( r1_orders_2(sK1,sK4,sK3) | k12_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_992,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK3) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1867,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK3) = iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1838,c_992]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X2)
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v2_lattice3(X0)
% 3.27/0.99      | v2_struct_0(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_0,plain,
% 3.27/0.99      ( ~ l1_orders_2(X0) | ~ v2_lattice3(X0) | ~ v2_struct_0(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_152,plain,
% 3.27/0.99      ( ~ v2_lattice3(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2,c_0]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_153,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X2)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v2_lattice3(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_152]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_296,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X2)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1
% 3.27/0.99      | sK1 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_153,c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_297,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/0.99      | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X2)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | ~ v5_orders_2(sK1)
% 3.27/0.99      | ~ l1_orders_2(sK1)
% 3.27/0.99      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_296]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_301,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/0.99      | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X2)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_297,c_21,c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_302,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/0.99      | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X2)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_301]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_668,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0_43,X2_43)
% 3.27/0.99      | r1_orders_2(sK1,sK0(sK1,X1_43,X2_43,X0_43),X2_43)
% 3.27/0.99      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,X1_43,X2_43) = X0_43 ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_302]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_998,plain,
% 3.27/0.99      ( k11_lattice3(sK1,X0_43,X1_43) = X2_43
% 3.27/0.99      | r1_orders_2(sK1,X2_43,X0_43) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,X2_43,X1_43) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,sK0(sK1,X0_43,X1_43,X2_43),X1_43) = iProver_top
% 3.27/0.99      | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v2_lattice3(X0)
% 3.27/0.99      | v2_struct_0(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_157,plain,
% 3.27/0.99      ( ~ v2_lattice3(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1,c_0]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_158,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v2_lattice3(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_157]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_263,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1
% 3.27/0.99      | sK1 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_158,c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_264,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X0)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | ~ v5_orders_2(sK1)
% 3.27/0.99      | ~ l1_orders_2(sK1)
% 3.27/0.99      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_263]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_268,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X0)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_264,c_21,c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_269,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X0)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_268]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_669,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0_43,X2_43)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK0(sK1,X1_43,X2_43,X0_43),X0_43)
% 3.27/0.99      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,X1_43,X2_43) = X0_43 ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_269]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_997,plain,
% 3.27/0.99      ( k11_lattice3(sK1,X0_43,X1_43) = X2_43
% 3.27/0.99      | r1_orders_2(sK1,X2_43,X0_43) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,X2_43,X1_43) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,sK0(sK1,X0_43,X1_43,X2_43),X2_43) != iProver_top
% 3.27/0.99      | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2689,plain,
% 3.27/0.99      ( k11_lattice3(sK1,X0_43,X1_43) = X1_43
% 3.27/0.99      | r1_orders_2(sK1,X1_43,X0_43) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,X1_43,X1_43) != iProver_top
% 3.27/0.99      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_998,c_997]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2995,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | k11_lattice3(sK1,sK3,sK4) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK4) != iProver_top
% 3.27/0.99      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1867,c_2689]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_26,plain,
% 3.27/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_16,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_27,plain,
% 3.27/0.99      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_15,negated_conjecture,
% 3.27/0.99      ( r1_orders_2(sK1,sK4,sK2) | k12_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_673,negated_conjecture,
% 3.27/0.99      ( r1_orders_2(sK1,sK4,sK2) | k12_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_993,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK2) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_13,negated_conjecture,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0,sK2)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0,sK3)
% 3.27/0.99      | r1_orders_2(sK1,X0,sK4)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | k12_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_675,negated_conjecture,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0_43,sK2)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0_43,sK3)
% 3.27/0.99      | r1_orders_2(sK1,X0_43,sK4)
% 3.27/0.99      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/0.99      | k12_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_991,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,X0_43,sK2) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,X0_43,sK3) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,X0_43,sK4) = iProver_top
% 3.27/0.99      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1541,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK4) = iProver_top
% 3.27/0.99      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_993,c_991]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_698,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK3) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1656,plain,
% 3.27/0.99      ( r1_orders_2(sK1,sK4,sK4) = iProver_top
% 3.27/0.99      | k12_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_1541,c_27,c_698]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1657,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK4) = iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_1656]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1864,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK4) = iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1838,c_1657]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3191,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK3,sK4) = sK4
% 3.27/0.99      | k11_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_2995,c_26,c_27,c_1864]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3192,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | k11_lattice3(sK1,sK3,sK4) = sK4 ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_3191]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7,plain,
% 3.27/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v2_lattice3(X0)
% 3.27/0.99      | v2_struct_0(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_119,plain,
% 3.27/0.99      ( ~ v2_lattice3(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) ),
% 3.27/0.99      inference(global_propositional_subsumption,[status(thm)],[c_7,c_0]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_120,plain,
% 3.27/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v2_lattice3(X0) ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_119]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_448,plain,
% 3.27/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | sK1 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_120,c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_449,plain,
% 3.27/0.99      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X0)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1))
% 3.27/0.99      | ~ v5_orders_2(sK1)
% 3.27/0.99      | ~ l1_orders_2(sK1) ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_448]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_451,plain,
% 3.27/0.99      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X0)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_449,c_21,c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_663,plain,
% 3.27/0.99      ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X0_43)
% 3.27/0.99      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_451]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1003,plain,
% 3.27/0.99      ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X0_43) = iProver_top
% 3.27/0.99      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3195,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK3,sK4) = sK4
% 3.27/0.99      | r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2) = iProver_top
% 3.27/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_3192,c_1003]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_25,plain,
% 3.27/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_684,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0_43,X0_44)
% 3.27/0.99      | m1_subset_1(X1_43,X0_44)
% 3.27/0.99      | X1_43 != X0_43 ),
% 3.27/0.99      theory(equality) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1305,plain,
% 3.27/0.99      ( m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 3.27/0.99      | X0_43 != sK4 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_684]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1370,plain,
% 3.27/0.99      ( m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,X0_43,X1_43) != sK4 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1823,plain,
% 3.27/0.99      ( m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1370]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1824,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK2,sK3) != sK4
% 3.27/0.99      | m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) = iProver_top
% 3.27/0.99      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1823]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2062,plain,
% 3.27/0.99      ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2)
% 3.27/0.99      | ~ m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_663]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2063,plain,
% 3.27/0.99      ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2) = iProver_top
% 3.27/0.99      | m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_2062]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1865,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK2) = iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1838,c_993]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_12,negated_conjecture,
% 3.27/0.99      ( ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/0.99      | m1_subset_1(sK5,u1_struct_0(sK1))
% 3.27/0.99      | k12_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_676,negated_conjecture,
% 3.27/0.99      ( ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/0.99      | m1_subset_1(sK5,u1_struct_0(sK1))
% 3.27/0.99      | k12_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_990,plain,
% 3.27/0.99      ( k12_lattice3(sK1,sK2,sK3) != sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/0.99      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1869,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK2,sK3) != sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/0.99      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1838,c_990]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3201,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK3,sK4) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/0.99      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_3192,c_1869]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1280,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,sK0(sK1,sK2,X0_43,sK4),sK4)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK4,X0_43)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/0.99      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,sK2,X0_43) = sK4 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_669]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1484,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK4),sK4)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/0.99      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 3.27/0.99      | k11_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1280]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1485,plain,
% 3.27/0.99      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/0.99      | r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK4),sK4) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/0.99      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/0.99      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1484]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v2_lattice3(X0)
% 3.27/0.99      | v2_struct_0(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_145,plain,
% 3.27/0.99      ( ~ v2_lattice3(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3,c_0]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_146,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | ~ v2_lattice3(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_145]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_329,plain,
% 3.27/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_orders_2(X0,X1,X3)
% 3.27/0.99      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 3.27/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/0.99      | ~ v5_orders_2(X0)
% 3.27/0.99      | ~ l1_orders_2(X0)
% 3.27/0.99      | k11_lattice3(X0,X3,X2) = X1
% 3.27/0.99      | sK1 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_146,c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_330,plain,
% 3.27/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/0.99      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/0.99      | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X1)
% 3.27/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/0.99      | ~ v5_orders_2(sK1)
% 3.27/0.99      | ~ l1_orders_2(sK1)
% 3.27/0.99      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_329]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_332,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X1)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_330,c_21,c_19]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_333,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,X1,X2,X0),X1)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/1.00      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_332]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_667,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0_43,X2_43)
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,X1_43,X2_43,X0_43),X1_43)
% 3.27/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 3.27/1.00      | k11_lattice3(sK1,X1_43,X2_43) = X0_43 ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_333]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_999,plain,
% 3.27/1.00      ( k11_lattice3(sK1,X0_43,X1_43) = X2_43
% 3.27/1.00      | r1_orders_2(sK1,X2_43,X0_43) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X2_43,X1_43) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,X0_43,X1_43,X2_43),X0_43) = iProver_top
% 3.27/1.00      | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1866,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK4) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(demodulation,[status(thm)],[c_1838,c_991]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2819,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,X0_43) = X1_43
% 3.27/1.00      | k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/1.00      | r1_orders_2(sK1,X1_43,X0_43) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X1_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,sK2,X0_43,X1_43),sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,sK2,X0_43,X1_43),sK4) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_999,c_1866]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4,plain,
% 3.27/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | m1_subset_1(sK0(X0,X3,X2,X1),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v2_lattice3(X0)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_138,plain,
% 3.27/1.00      ( ~ v2_lattice3(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | m1_subset_1(sK0(X0,X3,X2,X1),u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X2)
% 3.27/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4,c_0]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_139,plain,
% 3.27/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | m1_subset_1(sK0(X0,X3,X2,X1),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v2_lattice3(X0)
% 3.27/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_138]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_358,plain,
% 3.27/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | m1_subset_1(sK0(X0,X3,X2,X1),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | k11_lattice3(X0,X3,X2) = X1
% 3.27/1.00      | sK1 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_139,c_20]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_359,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | m1_subset_1(sK0(sK1,X1,X2,X0),u1_struct_0(sK1))
% 3.27/1.00      | ~ v5_orders_2(sK1)
% 3.27/1.00      | ~ l1_orders_2(sK1)
% 3.27/1.00      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_358]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_363,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | m1_subset_1(sK0(sK1,X1,X2,X0),u1_struct_0(sK1))
% 3.27/1.00      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_359,c_21,c_19]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_364,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/1.00      | m1_subset_1(sK0(sK1,X1,X2,X0),u1_struct_0(sK1))
% 3.27/1.00      | k11_lattice3(sK1,X1,X2) = X0 ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_363]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_666,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0_43,X2_43)
% 3.27/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 3.27/1.00      | m1_subset_1(sK0(sK1,X1_43,X2_43,X0_43),u1_struct_0(sK1))
% 3.27/1.00      | k11_lattice3(sK1,X1_43,X2_43) = X0_43 ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_364]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1775,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0_43,sK2)
% 3.27/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/1.00      | m1_subset_1(sK0(sK1,sK2,X1_43,X0_43),u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.27/1.00      | k11_lattice3(sK1,sK2,X1_43) = X0_43 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_666]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1779,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,X0_43) = X1_43
% 3.27/1.00      | r1_orders_2(sK1,X1_43,X0_43) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X1_43,sK2) != iProver_top
% 3.27/1.00      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK0(sK1,sK2,X0_43,X1_43),u1_struct_0(sK1)) = iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3473,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,X0_43) = X1_43
% 3.27/1.00      | k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/1.00      | r1_orders_2(sK1,X1_43,X0_43) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X1_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,sK2,X0_43,X1_43),sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,sK2,X0_43,X1_43),sK4) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2819,c_25,c_1779]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3487,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,sK3) = X0_43
% 3.27/1.00      | k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_43),sK4) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_998,c_3473]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3489,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/1.00      | r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK4),sK4) = iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_3487]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3492,plain,
% 3.27/1.00      ( r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_3201,c_25,c_26,c_27,c_1485,c_1865,c_1867,c_1869,
% 3.27/1.00                 c_3489]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3499,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,sK3) = sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_1865,c_3492]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3649,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_3499,c_25,c_26,c_27,c_1485,c_1865,c_1867,c_3489]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3799,plain,
% 3.27/1.00      ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2) = iProver_top ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_3195,c_25,c_26,c_27,c_1485,c_1824,c_1865,c_1867,
% 3.27/1.00                 c_2063,c_3489]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3803,plain,
% 3.27/1.00      ( r1_orders_2(sK1,sK4,sK2) = iProver_top ),
% 3.27/1.00      inference(light_normalisation,[status(thm)],[c_3799,c_3649]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11,negated_conjecture,
% 3.27/1.00      ( ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/1.00      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK2)
% 3.27/1.00      | k12_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_677,negated_conjecture,
% 3.27/1.00      ( ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/1.00      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK2)
% 3.27/1.00      | k12_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_989,plain,
% 3.27/1.00      ( k12_lattice3(sK1,sK2,sK3) != sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1870,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK2,sK3) != sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
% 3.27/1.00      inference(demodulation,[status(thm)],[c_1838,c_989]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3200,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK3,sK4) = sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_3192,c_1870]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3807,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK3,sK4) = sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_3803,c_3200]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_693,plain,
% 3.27/1.00      ( k12_lattice3(sK1,sK2,sK3) != sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK2) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3658,plain,
% 3.27/1.00      ( k12_lattice3(sK1,sK2,sK3) = sK4 ),
% 3.27/1.00      inference(demodulation,[status(thm)],[c_3649,c_1838]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_6,plain,
% 3.27/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v2_lattice3(X0)
% 3.27/1.00      | v2_struct_0(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_126,plain,
% 3.27/1.00      ( ~ v2_lattice3(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) ),
% 3.27/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6,c_0]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_127,plain,
% 3.27/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v2_lattice3(X0) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_126]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_424,plain,
% 3.27/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | sK1 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_127,c_20]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_425,plain,
% 3.27/1.00      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1))
% 3.27/1.00      | ~ v5_orders_2(sK1)
% 3.27/1.00      | ~ l1_orders_2(sK1) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_424]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_429,plain,
% 3.27/1.00      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_425,c_21,c_19]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_664,plain,
% 3.27/1.00      ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X1_43)
% 3.27/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_429]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1002,plain,
% 3.27/1.00      ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X1_43) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3687,plain,
% 3.27/1.00      ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK3) = iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_3649,c_1002]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3708,plain,
% 3.27/1.00      ( r1_orders_2(sK1,sK4,sK3) = iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(light_normalisation,[status(thm)],[c_3687,c_3649]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3686,plain,
% 3.27/1.00      ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK2) = iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_3649,c_1003]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3717,plain,
% 3.27/1.00      ( r1_orders_2(sK1,sK4,sK2) = iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(light_normalisation,[status(thm)],[c_3686,c_3649]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4852,plain,
% 3.27/1.00      ( r1_orders_2(sK1,sK5,sK2) = iProver_top ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_3807,c_25,c_26,c_27,c_693,c_3658,c_3708,c_3717]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5,plain,
% 3.27/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.27/1.00      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v2_lattice3(X0)
% 3.27/1.00      | v2_struct_0(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_131,plain,
% 3.27/1.00      ( ~ v2_lattice3(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X2) ),
% 3.27/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5,c_0]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_132,plain,
% 3.27/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.27/1.00      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | ~ v2_lattice3(X0) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_131]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_391,plain,
% 3.27/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.27/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.27/1.00      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
% 3.27/1.00      | ~ v5_orders_2(X0)
% 3.27/1.00      | ~ l1_orders_2(X0)
% 3.27/1.00      | sK1 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_132,c_20]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_392,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/1.00      | r1_orders_2(sK1,X0,k11_lattice3(sK1,X1,X2))
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,X1,X2),u1_struct_0(sK1))
% 3.27/1.00      | ~ v5_orders_2(sK1)
% 3.27/1.00      | ~ l1_orders_2(sK1) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_396,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/1.00      | r1_orders_2(sK1,X0,k11_lattice3(sK1,X1,X2))
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,X1,X2),u1_struct_0(sK1)) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_392,c_21,c_19]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_397,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0,X2)
% 3.27/1.00      | r1_orders_2(sK1,X0,k11_lattice3(sK1,X1,X2))
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,X1,X2),u1_struct_0(sK1)) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_396]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_665,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0_43,X2_43)
% 3.27/1.00      | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,X1_43,X2_43))
% 3.27/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,X1_43,X2_43),u1_struct_0(sK1)) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_397]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1001,plain,
% 3.27/1.00      ( r1_orders_2(sK1,X0_43,X1_43) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,X2_43) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,X1_43,X2_43)) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(X2_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(k11_lattice3(sK1,X1_43,X2_43),u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3197,plain,
% 3.27/1.00      ( k11_lattice3(sK1,sK3,sK4) = sK4
% 3.27/1.00      | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3)) = iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK3) != iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_3192,c_1001]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1776,plain,
% 3.27/1.00      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 3.27/1.00      | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,X1_43))
% 3.27/1.00      | ~ r1_orders_2(sK1,X0_43,sK2)
% 3.27/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,sK2,X1_43),u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_665]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3934,plain,
% 3.27/1.00      ( r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3))
% 3.27/1.00      | ~ r1_orders_2(sK1,X0_43,sK2)
% 3.27/1.00      | ~ r1_orders_2(sK1,X0_43,sK3)
% 3.27/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.27/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_1776]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3935,plain,
% 3.27/1.00      ( r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3)) = iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK3) != iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(k11_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_3934]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4390,plain,
% 3.27/1.00      ( m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3)) = iProver_top ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_3197,c_25,c_26,c_27,c_1485,c_1824,c_1865,c_1867,
% 3.27/1.00                 c_3489,c_3935]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4391,plain,
% 3.27/1.00      ( r1_orders_2(sK1,X0_43,k11_lattice3(sK1,sK2,sK3)) = iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK3) != iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_4390]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4396,plain,
% 3.27/1.00      ( r1_orders_2(sK1,X0_43,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,X0_43,sK4) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(light_normalisation,[status(thm)],[c_4391,c_3649]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4858,plain,
% 3.27/1.00      ( r1_orders_2(sK1,sK5,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK4) = iProver_top
% 3.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_4852,c_4396]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_694,plain,
% 3.27/1.00      ( k12_lattice3(sK1,sK2,sK3) != sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10,negated_conjecture,
% 3.27/1.00      ( ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/1.00      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK3)
% 3.27/1.00      | k12_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_678,negated_conjecture,
% 3.27/1.00      ( ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/1.00      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK3)
% 3.27/1.00      | k12_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_692,plain,
% 3.27/1.00      ( k12_lattice3(sK1,sK2,sK3) != sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK3) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9,negated_conjecture,
% 3.27/1.00      ( ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/1.00      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/1.00      | ~ r1_orders_2(sK1,sK5,sK4)
% 3.27/1.00      | k12_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_679,negated_conjecture,
% 3.27/1.00      ( ~ r1_orders_2(sK1,sK4,sK2)
% 3.27/1.00      | ~ r1_orders_2(sK1,sK4,sK3)
% 3.27/1.00      | ~ r1_orders_2(sK1,sK5,sK4)
% 3.27/1.00      | k12_lattice3(sK1,sK2,sK3) != sK4 ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_691,plain,
% 3.27/1.00      ( k12_lattice3(sK1,sK2,sK3) != sK4
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK2) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK4,sK3) != iProver_top
% 3.27/1.00      | r1_orders_2(sK1,sK5,sK4) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(contradiction,plain,
% 3.27/1.00      ( $false ),
% 3.27/1.00      inference(minisat,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_4858,c_3717,c_3708,c_3658,c_694,c_692,c_691,c_27,c_26,
% 3.27/1.00                 c_25]) ).
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/1.00  
% 3.27/1.00  ------                               Statistics
% 3.27/1.00  
% 3.27/1.00  ------ General
% 3.27/1.00  
% 3.27/1.00  abstr_ref_over_cycles:                  0
% 3.27/1.00  abstr_ref_under_cycles:                 0
% 3.27/1.00  gc_basic_clause_elim:                   0
% 3.27/1.00  forced_gc_time:                         0
% 3.27/1.00  parsing_time:                           0.009
% 3.27/1.00  unif_index_cands_time:                  0.
% 3.27/1.00  unif_index_add_time:                    0.
% 3.27/1.00  orderings_time:                         0.
% 3.27/1.00  out_proof_time:                         0.015
% 3.27/1.00  total_time:                             0.19
% 3.27/1.00  num_of_symbols:                         46
% 3.27/1.00  num_of_terms:                           3624
% 3.27/1.00  
% 3.27/1.00  ------ Preprocessing
% 3.27/1.00  
% 3.27/1.00  num_of_splits:                          0
% 3.27/1.00  num_of_split_atoms:                     0
% 3.27/1.00  num_of_reused_defs:                     0
% 3.27/1.00  num_eq_ax_congr_red:                    24
% 3.27/1.00  num_of_sem_filtered_clauses:            2
% 3.27/1.00  num_of_subtypes:                        3
% 3.27/1.00  monotx_restored_types:                  0
% 3.27/1.00  sat_num_of_epr_types:                   0
% 3.27/1.00  sat_num_of_non_cyclic_types:            0
% 3.27/1.00  sat_guarded_non_collapsed_types:        1
% 3.27/1.00  num_pure_diseq_elim:                    0
% 3.27/1.00  simp_replaced_by:                       0
% 3.27/1.00  res_preprocessed:                       87
% 3.27/1.00  prep_upred:                             0
% 3.27/1.00  prep_unflattend:                        8
% 3.27/1.00  smt_new_axioms:                         0
% 3.27/1.00  pred_elim_cands:                        2
% 3.27/1.00  pred_elim:                              3
% 3.27/1.00  pred_elim_cl:                           3
% 3.27/1.00  pred_elim_cycles:                       5
% 3.27/1.00  merged_defs:                            0
% 3.27/1.00  merged_defs_ncl:                        0
% 3.27/1.00  bin_hyper_res:                          0
% 3.27/1.00  prep_cycles:                            4
% 3.27/1.00  pred_elim_time:                         0.006
% 3.27/1.00  splitting_time:                         0.
% 3.27/1.00  sem_filter_time:                        0.
% 3.27/1.00  monotx_time:                            0.
% 3.27/1.00  subtype_inf_time:                       0.
% 3.27/1.00  
% 3.27/1.00  ------ Problem properties
% 3.27/1.00  
% 3.27/1.00  clauses:                                18
% 3.27/1.00  conjectures:                            10
% 3.27/1.00  epr:                                    0
% 3.27/1.00  horn:                                   12
% 3.27/1.00  ground:                                 9
% 3.27/1.00  unary:                                  3
% 3.27/1.00  binary:                                 2
% 3.27/1.00  lits:                                   74
% 3.27/1.00  lits_eq:                                12
% 3.27/1.00  fd_pure:                                0
% 3.27/1.00  fd_pseudo:                              0
% 3.27/1.00  fd_cond:                                0
% 3.27/1.00  fd_pseudo_cond:                         4
% 3.27/1.00  ac_symbols:                             0
% 3.27/1.00  
% 3.27/1.00  ------ Propositional Solver
% 3.27/1.00  
% 3.27/1.00  prop_solver_calls:                      26
% 3.27/1.00  prop_fast_solver_calls:                 1150
% 3.27/1.00  smt_solver_calls:                       0
% 3.27/1.00  smt_fast_solver_calls:                  0
% 3.27/1.00  prop_num_of_clauses:                    1440
% 3.27/1.00  prop_preprocess_simplified:             3834
% 3.27/1.00  prop_fo_subsumed:                       50
% 3.27/1.00  prop_solver_time:                       0.
% 3.27/1.00  smt_solver_time:                        0.
% 3.27/1.00  smt_fast_solver_time:                   0.
% 3.27/1.00  prop_fast_solver_time:                  0.
% 3.27/1.00  prop_unsat_core_time:                   0.
% 3.27/1.00  
% 3.27/1.00  ------ QBF
% 3.27/1.00  
% 3.27/1.00  qbf_q_res:                              0
% 3.27/1.00  qbf_num_tautologies:                    0
% 3.27/1.00  qbf_prep_cycles:                        0
% 3.27/1.00  
% 3.27/1.00  ------ BMC1
% 3.27/1.00  
% 3.27/1.00  bmc1_current_bound:                     -1
% 3.27/1.00  bmc1_last_solved_bound:                 -1
% 3.27/1.00  bmc1_unsat_core_size:                   -1
% 3.27/1.00  bmc1_unsat_core_parents_size:           -1
% 3.27/1.00  bmc1_merge_next_fun:                    0
% 3.27/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.27/1.00  
% 3.27/1.00  ------ Instantiation
% 3.27/1.00  
% 3.27/1.00  inst_num_of_clauses:                    441
% 3.27/1.00  inst_num_in_passive:                    87
% 3.27/1.00  inst_num_in_active:                     258
% 3.27/1.00  inst_num_in_unprocessed:                96
% 3.27/1.00  inst_num_of_loops:                      290
% 3.27/1.00  inst_num_of_learning_restarts:          0
% 3.27/1.00  inst_num_moves_active_passive:          29
% 3.27/1.00  inst_lit_activity:                      0
% 3.27/1.00  inst_lit_activity_moves:                0
% 3.27/1.00  inst_num_tautologies:                   0
% 3.27/1.00  inst_num_prop_implied:                  0
% 3.27/1.00  inst_num_existing_simplified:           0
% 3.27/1.00  inst_num_eq_res_simplified:             0
% 3.27/1.00  inst_num_child_elim:                    0
% 3.27/1.00  inst_num_of_dismatching_blockings:      405
% 3.27/1.00  inst_num_of_non_proper_insts:           472
% 3.27/1.00  inst_num_of_duplicates:                 0
% 3.27/1.00  inst_inst_num_from_inst_to_res:         0
% 3.27/1.00  inst_dismatching_checking_time:         0.
% 3.27/1.00  
% 3.27/1.00  ------ Resolution
% 3.27/1.00  
% 3.27/1.00  res_num_of_clauses:                     0
% 3.27/1.00  res_num_in_passive:                     0
% 3.27/1.00  res_num_in_active:                      0
% 3.27/1.00  res_num_of_loops:                       91
% 3.27/1.00  res_forward_subset_subsumed:            4
% 3.27/1.00  res_backward_subset_subsumed:           0
% 3.27/1.00  res_forward_subsumed:                   0
% 3.27/1.00  res_backward_subsumed:                  0
% 3.27/1.00  res_forward_subsumption_resolution:     0
% 3.27/1.00  res_backward_subsumption_resolution:    0
% 3.27/1.00  res_clause_to_clause_subsumption:       676
% 3.27/1.00  res_orphan_elimination:                 0
% 3.27/1.00  res_tautology_del:                      19
% 3.27/1.00  res_num_eq_res_simplified:              0
% 3.27/1.00  res_num_sel_changes:                    0
% 3.27/1.00  res_moves_from_active_to_pass:          0
% 3.27/1.00  
% 3.27/1.00  ------ Superposition
% 3.27/1.00  
% 3.27/1.00  sup_time_total:                         0.
% 3.27/1.00  sup_time_generating:                    0.
% 3.27/1.00  sup_time_sim_full:                      0.
% 3.27/1.00  sup_time_sim_immed:                     0.
% 3.27/1.00  
% 3.27/1.00  sup_num_of_clauses:                     70
% 3.27/1.00  sup_num_in_active:                      37
% 3.27/1.00  sup_num_in_passive:                     33
% 3.27/1.00  sup_num_of_loops:                       56
% 3.27/1.00  sup_fw_superposition:                   44
% 3.27/1.00  sup_bw_superposition:                   33
% 3.27/1.00  sup_immediate_simplified:               7
% 3.27/1.00  sup_given_eliminated:                   0
% 3.27/1.00  comparisons_done:                       0
% 3.27/1.00  comparisons_avoided:                    6
% 3.27/1.00  
% 3.27/1.00  ------ Simplifications
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  sim_fw_subset_subsumed:                 4
% 3.27/1.00  sim_bw_subset_subsumed:                 13
% 3.27/1.00  sim_fw_subsumed:                        0
% 3.27/1.00  sim_bw_subsumed:                        0
% 3.27/1.00  sim_fw_subsumption_res:                 0
% 3.27/1.00  sim_bw_subsumption_res:                 0
% 3.27/1.00  sim_tautology_del:                      0
% 3.27/1.00  sim_eq_tautology_del:                   2
% 3.27/1.00  sim_eq_res_simp:                        4
% 3.27/1.00  sim_fw_demodulated:                     0
% 3.27/1.00  sim_bw_demodulated:                     15
% 3.27/1.00  sim_light_normalised:                   6
% 3.27/1.00  sim_joinable_taut:                      0
% 3.27/1.00  sim_joinable_simp:                      0
% 3.27/1.00  sim_ac_normalised:                      0
% 3.27/1.00  sim_smt_subsumption:                    0
% 3.27/1.00  
%------------------------------------------------------------------------------
