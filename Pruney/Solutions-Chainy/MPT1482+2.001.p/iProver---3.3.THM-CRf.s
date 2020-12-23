%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:00 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  164 (2563 expanded)
%              Number of clauses        :  112 ( 707 expanded)
%              Number of leaves         :   14 ( 771 expanded)
%              Depth                    :   33
%              Number of atoms          : 1056 (18131 expanded)
%              Number of equality atoms :  256 (2818 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
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
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k11_lattice3(X0,X1,sK9) != k11_lattice3(X0,sK9,X1)
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k11_lattice3(X0,X2,sK8) != k11_lattice3(X0,sK8,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(sK7,X1,X2) != k11_lattice3(sK7,X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK7)) )
          & m1_subset_1(X1,u1_struct_0(sK7)) )
      & l1_orders_2(sK7)
      & v2_lattice3(sK7)
      & v5_orders_2(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k11_lattice3(sK7,sK8,sK9) != k11_lattice3(sK7,sK9,sK8)
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l1_orders_2(sK7)
    & v2_lattice3(sK7)
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

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,(
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

fof(f20,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f23,f22,f21,f20])).

fof(f37,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    v2_lattice3(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,X8,sK5(X0,X5,X6))
      | ~ r1_orders_2(X0,X8,X6)
      | ~ r1_orders_2(X0,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
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
      ( ( ( v2_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK5(X0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK5(X0,X5,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f60,plain,(
    k11_lattice3(sK7,sK8,sK9) != k11_lattice3(sK7,sK9,sK8) ),
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

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_171,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,sK6(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_0])).

cnf(c_172,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_419,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_26])).

cnf(c_420,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_25,negated_conjecture,
    ( v2_lattice3(sK7) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_422,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_25,c_24])).

cnf(c_423,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_2405,plain,
    ( ~ r1_orders_2(sK7,X0_47,X1_47)
    | ~ r1_orders_2(sK7,X0_47,X2_47)
    | r1_orders_2(sK7,sK6(sK7,X1_47,X2_47,X0_47),X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1_47,X2_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_2772,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = X2_47
    | r1_orders_2(sK7,X2_47,X0_47) != iProver_top
    | r1_orders_2(sK7,X2_47,X1_47) != iProver_top
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,X2_47),X0_47) = iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2405])).

cnf(c_15,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_178,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,sK6(X0,X3,X2,X1),X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_0])).

cnf(c_179,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_386,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_26])).

cnf(c_387,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_391,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_25,c_24])).

cnf(c_392,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_2406,plain,
    ( ~ r1_orders_2(sK7,X0_47,X1_47)
    | ~ r1_orders_2(sK7,X0_47,X2_47)
    | r1_orders_2(sK7,sK6(sK7,X1_47,X2_47,X0_47),X2_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1_47,X2_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_2771,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = X2_47
    | r1_orders_2(sK7,X2_47,X0_47) != iProver_top
    | r1_orders_2(sK7,X2_47,X1_47) != iProver_top
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,X2_47),X1_47) = iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2406])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,sK5(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2414,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | ~ r1_orders_2(X0_46,X0_47,X2_47)
    | r1_orders_2(X0_46,X0_47,sK5(X0_46,X2_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
    | ~ sP0(X0_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2764,plain,
    ( r1_orders_2(X0_46,X0_47,X1_47) != iProver_top
    | r1_orders_2(X0_46,X0_47,X2_47) != iProver_top
    | r1_orders_2(X0_46,X0_47,sK5(X0_46,X2_47,X1_47)) = iProver_top
    | m1_subset_1(X2_47,u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | sP0(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK6(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_183,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK6(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_0])).

cnf(c_184,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK6(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_353,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK6(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_26])).

cnf(c_354,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | ~ r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_358,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | ~ r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_25,c_24])).

cnf(c_359,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | ~ r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_2407,plain,
    ( ~ r1_orders_2(sK7,X0_47,X1_47)
    | ~ r1_orders_2(sK7,X0_47,X2_47)
    | ~ r1_orders_2(sK7,sK6(sK7,X1_47,X2_47,X0_47),X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | k11_lattice3(sK7,X1_47,X2_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_2770,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = X2_47
    | r1_orders_2(sK7,X2_47,X0_47) != iProver_top
    | r1_orders_2(sK7,X2_47,X1_47) != iProver_top
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,X2_47),X2_47) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2407])).

cnf(c_4295,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X3_47) != iProver_top
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X2_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X0_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X1_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2764,c_2770])).

cnf(c_28,plain,
    ( v2_lattice3(sK7) = iProver_top ),
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
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_80,plain,
    ( sP1(X0) != iProver_top
    | sP0(X0) = iProver_top
    | v2_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_82,plain,
    ( sP1(sK7) != iProver_top
    | sP0(sK7) = iProver_top
    | v2_lattice3(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_17,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_164,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK6(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_0])).

cnf(c_165,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_448,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_165,c_26])).

cnf(c_449,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X1,X2,X0),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_453,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X1,X2,X0),u1_struct_0(sK7))
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_25,c_24])).

cnf(c_454,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X1,X2,X0),u1_struct_0(sK7))
    | k11_lattice3(sK7,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_2404,plain,
    ( ~ r1_orders_2(sK7,X0_47,X1_47)
    | ~ r1_orders_2(sK7,X0_47,X2_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X1_47,X2_47,X0_47),u1_struct_0(sK7))
    | k11_lattice3(sK7,X1_47,X2_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_4052,plain,
    ( ~ r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X2_47)
    | ~ r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X3_47)
    | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X3_47,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X2_47,X3_47,sK5(sK7,X0_47,X1_47)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7))
    | k11_lattice3(sK7,X2_47,X3_47) = sK5(sK7,X0_47,X1_47) ),
    inference(instantiation,[status(thm)],[c_2404])).

cnf(c_4058,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
    | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X0_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X1_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4052])).

cnf(c_4464,plain,
    ( m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top
    | k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X3_47) != iProver_top
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X2_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X0_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X1_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4295,c_28,c_29,c_51,c_82,c_4058])).

cnf(c_4465,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X3_47) != iProver_top
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X2_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X0_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X1_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4464])).

cnf(c_4481,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X1_47)
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X1_47)),X2_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X1_47),X1_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X1_47),X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2771,c_4465])).

cnf(c_4561,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X0_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X1_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2772,c_4481])).

cnf(c_11,plain,
    ( r1_orders_2(X0,sK5(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2412,plain,
    ( r1_orders_2(X0_46,sK5(X0_46,X0_47,X1_47),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ sP0(X0_46) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3014,plain,
    ( r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_2412])).

cnf(c_3020,plain,
    ( r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3014])).

cnf(c_10,plain,
    ( r1_orders_2(X0,sK5(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2413,plain,
    ( r1_orders_2(X0_46,sK5(X0_46,X0_47,X1_47),X1_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ sP0(X0_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3040,plain,
    ( r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_2413])).

cnf(c_3046,plain,
    ( r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X1_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3040])).

cnf(c_4813,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4561,c_28,c_29,c_51,c_82,c_3020,c_3046])).

cnf(c_4823,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2767,c_4813])).

cnf(c_5370,plain,
    ( m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4823,c_28,c_29,c_51,c_82])).

cnf(c_5371,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5370])).

cnf(c_5379,plain,
    ( k11_lattice3(sK7,sK9,X0_47) = sK5(sK7,sK9,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2768,c_5371])).

cnf(c_5482,plain,
    ( k11_lattice3(sK7,sK9,sK8) = sK5(sK7,sK9,sK8) ),
    inference(superposition,[status(thm)],[c_2769,c_5379])).

cnf(c_19,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_152,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_0])).

cnf(c_153,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_514,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_26])).

cnf(c_515,plain,
    ( r1_orders_2(sK7,k11_lattice3(sK7,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k11_lattice3(sK7,X0,X1),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7)
    | ~ v2_lattice3(sK7) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_519,plain,
    ( r1_orders_2(sK7,k11_lattice3(sK7,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k11_lattice3(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_25,c_24])).

cnf(c_2402,plain,
    ( r1_orders_2(sK7,k11_lattice3(sK7,X0_47,X1_47),X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(k11_lattice3(sK7,X0_47,X1_47),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_519])).

cnf(c_2775,plain,
    ( r1_orders_2(sK7,k11_lattice3(sK7,X0_47,X1_47),X1_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k11_lattice3(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2402])).

cnf(c_5607,plain,
    ( r1_orders_2(sK7,k11_lattice3(sK7,sK9,sK8),sK8) = iProver_top
    | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5482,c_2775])).

cnf(c_5628,plain,
    ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK8) = iProver_top
    | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5607,c_5482])).

cnf(c_30,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4015,plain,
    ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK8)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_3040])).

cnf(c_4018,plain,
    ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK8) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4015])).

cnf(c_6288,plain,
    ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5628,c_28,c_29,c_30,c_31,c_51,c_82,c_4018])).

cnf(c_4482,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X0_47)
    | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X0_47)),X2_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X0_47),X0_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X2_47,X0_47),X1_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X2_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2772,c_4465])).

cnf(c_4966,plain,
    ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X1_47,X0_47)
    | r1_orders_2(sK7,sK5(sK7,X1_47,X0_47),X0_47) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X1_47,X0_47),X1_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X1_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2771,c_4482])).

cnf(c_6295,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK5(sK7,sK9,sK8)
    | r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK9) != iProver_top
    | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6288,c_4966])).

cnf(c_5380,plain,
    ( k11_lattice3(sK7,sK8,X0_47) = sK5(sK7,sK8,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2769,c_5371])).

cnf(c_5778,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK5(sK7,sK8,sK9) ),
    inference(superposition,[status(thm)],[c_2768,c_5380])).

cnf(c_6301,plain,
    ( sK5(sK7,sK8,sK9) = sK5(sK7,sK9,sK8)
    | r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK9) != iProver_top
    | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6295,c_5778])).

cnf(c_21,negated_conjecture,
    ( k11_lattice3(sK7,sK8,sK9) != k11_lattice3(sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2410,negated_conjecture,
    ( k11_lattice3(sK7,sK8,sK9) != k11_lattice3(sK7,sK9,sK8) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_5605,plain,
    ( k11_lattice3(sK7,sK8,sK9) != sK5(sK7,sK9,sK8) ),
    inference(demodulation,[status(thm)],[c_5482,c_2410])).

cnf(c_5816,plain,
    ( sK5(sK7,sK8,sK9) != sK5(sK7,sK9,sK8) ),
    inference(demodulation,[status(thm)],[c_5778,c_5605])).

cnf(c_5146,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,sK9,X0_47),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_2411])).

cnf(c_5147,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,sK9,X0_47),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5146])).

cnf(c_5149,plain,
    ( m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5147])).

cnf(c_3371,plain,
    ( r1_orders_2(sK7,sK5(sK7,sK9,X0_47),sK9)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ sP0(sK7) ),
    inference(instantiation,[status(thm)],[c_3014])).

cnf(c_3372,plain,
    ( r1_orders_2(sK7,sK5(sK7,sK9,X0_47),sK9) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3371])).

cnf(c_3374,plain,
    ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | sP0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3372])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6301,c_5816,c_5149,c_3374,c_82,c_51,c_31,c_30,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:21:40 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.59/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/1.00  
% 3.59/1.00  ------  iProver source info
% 3.59/1.00  
% 3.59/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.59/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/1.00  git: non_committed_changes: false
% 3.59/1.00  git: last_make_outside_of_git: false
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     num_symb
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       true
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  ------ Parsing...
% 3.59/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/1.00  ------ Proving...
% 3.59/1.00  ------ Problem Properties 
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  clauses                                 21
% 3.59/1.00  conjectures                             3
% 3.59/1.00  EPR                                     1
% 3.59/1.00  Horn                                    13
% 3.59/1.00  unary                                   4
% 3.59/1.00  binary                                  2
% 3.59/1.00  lits                                    90
% 3.59/1.00  lits eq                                 5
% 3.59/1.00  fd_pure                                 0
% 3.59/1.00  fd_pseudo                               0
% 3.59/1.00  fd_cond                                 0
% 3.59/1.00  fd_pseudo_cond                          4
% 3.59/1.00  AC symbols                              0
% 3.59/1.00  
% 3.59/1.00  ------ Schedule dynamic 5 is on 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  Current options:
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     none
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       false
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ Proving...
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS status Theorem for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  fof(f4,conjecture,(
% 3.59/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f5,negated_conjecture,(
% 3.59/1.00    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 3.59/1.00    inference(negated_conjecture,[],[f4])).
% 3.59/1.00  
% 3.59/1.00  fof(f12,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (? [X2] : (k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f5])).
% 3.59/1.00  
% 3.59/1.00  fof(f13,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (? [X2] : (k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0))),
% 3.59/1.00    inference(flattening,[],[f12])).
% 3.59/1.00  
% 3.59/1.00  fof(f32,plain,(
% 3.59/1.00    ( ! [X0,X1] : (? [X2] : (k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k11_lattice3(X0,X1,sK9) != k11_lattice3(X0,sK9,X1) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f31,plain,(
% 3.59/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k11_lattice3(X0,X2,sK8) != k11_lattice3(X0,sK8,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f30,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (? [X2] : (k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (k11_lattice3(sK7,X1,X2) != k11_lattice3(sK7,X2,X1) & m1_subset_1(X2,u1_struct_0(sK7))) & m1_subset_1(X1,u1_struct_0(sK7))) & l1_orders_2(sK7) & v2_lattice3(sK7) & v5_orders_2(sK7))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f33,plain,(
% 3.59/1.00    ((k11_lattice3(sK7,sK8,sK9) != k11_lattice3(sK7,sK9,sK8) & m1_subset_1(sK9,u1_struct_0(sK7))) & m1_subset_1(sK8,u1_struct_0(sK7))) & l1_orders_2(sK7) & v2_lattice3(sK7) & v5_orders_2(sK7)),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f13,f32,f31,f30])).
% 3.59/1.00  
% 3.59/1.00  fof(f58,plain,(
% 3.59/1.00    m1_subset_1(sK8,u1_struct_0(sK7))),
% 3.59/1.00    inference(cnf_transformation,[],[f33])).
% 3.59/1.00  
% 3.59/1.00  fof(f59,plain,(
% 3.59/1.00    m1_subset_1(sK9,u1_struct_0(sK7))),
% 3.59/1.00    inference(cnf_transformation,[],[f33])).
% 3.59/1.00  
% 3.59/1.00  fof(f14,plain,(
% 3.59/1.00    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))))),
% 3.59/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.59/1.00  
% 3.59/1.00  fof(f18,plain,(
% 3.59/1.00    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.59/1.00    inference(nnf_transformation,[],[f14])).
% 3.59/1.00  
% 3.59/1.00  fof(f19,plain,(
% 3.59/1.00    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X5] : (! [X6] : (? [X7] : (! [X8] : (r1_orders_2(X0,X8,X7) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X7,X6) & r1_orders_2(X0,X7,X5) & m1_subset_1(X7,u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.59/1.00    inference(rectify,[],[f18])).
% 3.59/1.00  
% 3.59/1.00  fof(f23,plain,(
% 3.59/1.00    ! [X6,X5,X0] : (? [X7] : (! [X8] : (r1_orders_2(X0,X8,X7) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X7,X6) & r1_orders_2(X0,X7,X5) & m1_subset_1(X7,u1_struct_0(X0))) => (! [X8] : (r1_orders_2(X0,X8,sK5(X0,X5,X6)) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,sK5(X0,X5,X6),X6) & r1_orders_2(X0,sK5(X0,X5,X6),X5) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f22,plain,(
% 3.59/1.00    ( ! [X2,X1] : (! [X3,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X3),X3) & r1_orders_2(X0,sK4(X0,X3),X2) & r1_orders_2(X0,sK4(X0,X3),X1) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f21,plain,(
% 3.59/1.00    ( ! [X1] : (! [X0] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,sK3(X0)) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,sK3(X0)) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f20,plain,(
% 3.59/1.00    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,sK2(X0)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,sK2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f24,plain,(
% 3.59/1.00    ! [X0] : ((sP0(X0) | ((! [X3] : ((~r1_orders_2(X0,sK4(X0,X3),X3) & r1_orders_2(X0,sK4(X0,X3),sK3(X0)) & r1_orders_2(X0,sK4(X0,X3),sK2(X0)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,sK3(X0)) | ~r1_orders_2(X0,X3,sK2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X5] : (! [X6] : ((! [X8] : (r1_orders_2(X0,X8,sK5(X0,X5,X6)) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,sK5(X0,X5,X6),X6) & r1_orders_2(X0,sK5(X0,X5,X6),X5) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f23,f22,f21,f20])).
% 3.59/1.00  
% 3.59/1.00  fof(f37,plain,(
% 3.59/1.00    ( ! [X6,X0,X5] : (m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f24])).
% 3.59/1.00  
% 3.59/1.00  fof(f3,axiom,(
% 3.59/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f10,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f3])).
% 3.59/1.00  
% 3.59/1.00  fof(f11,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f10])).
% 3.59/1.00  
% 3.59/1.00  fof(f25,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(nnf_transformation,[],[f11])).
% 3.59/1.00  
% 3.59/1.00  fof(f26,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f25])).
% 3.59/1.00  
% 3.59/1.00  fof(f27,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(rectify,[],[f26])).
% 3.59/1.00  
% 3.59/1.00  fof(f28,plain,(
% 3.59/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK6(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f29,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK6(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).
% 3.59/1.00  
% 3.59/1.00  fof(f52,plain,(
% 3.59/1.00    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK6(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f29])).
% 3.59/1.00  
% 3.59/1.00  fof(f1,axiom,(
% 3.59/1.00    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f6,plain,(
% 3.59/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f1])).
% 3.59/1.00  
% 3.59/1.00  fof(f7,plain,(
% 3.59/1.00    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(flattening,[],[f6])).
% 3.59/1.00  
% 3.59/1.00  fof(f34,plain,(
% 3.59/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f7])).
% 3.59/1.00  
% 3.59/1.00  fof(f55,plain,(
% 3.59/1.00    v5_orders_2(sK7)),
% 3.59/1.00    inference(cnf_transformation,[],[f33])).
% 3.59/1.00  
% 3.59/1.00  fof(f56,plain,(
% 3.59/1.00    v2_lattice3(sK7)),
% 3.59/1.00    inference(cnf_transformation,[],[f33])).
% 3.59/1.00  
% 3.59/1.00  fof(f57,plain,(
% 3.59/1.00    l1_orders_2(sK7)),
% 3.59/1.00    inference(cnf_transformation,[],[f33])).
% 3.59/1.00  
% 3.59/1.00  fof(f53,plain,(
% 3.59/1.00    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK6(X0,X1,X2,X3),X2) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f29])).
% 3.59/1.00  
% 3.59/1.00  fof(f40,plain,(
% 3.59/1.00    ( ! [X6,X0,X8,X5] : (r1_orders_2(X0,X8,sK5(X0,X5,X6)) | ~r1_orders_2(X0,X8,X6) | ~r1_orders_2(X0,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f24])).
% 3.59/1.00  
% 3.59/1.00  fof(f54,plain,(
% 3.59/1.00    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK6(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f29])).
% 3.59/1.00  
% 3.59/1.00  fof(f2,axiom,(
% 3.59/1.00    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f8,plain,(
% 3.59/1.00    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f2])).
% 3.59/1.00  
% 3.59/1.00  fof(f9,plain,(
% 3.59/1.00    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(flattening,[],[f8])).
% 3.59/1.00  
% 3.59/1.00  fof(f15,plain,(
% 3.59/1.00    ! [X0] : ((v2_lattice3(X0) <=> sP0(X0)) | ~sP1(X0))),
% 3.59/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.59/1.00  
% 3.59/1.00  fof(f16,plain,(
% 3.59/1.00    ! [X0] : (sP1(X0) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(definition_folding,[],[f9,f15,f14])).
% 3.59/1.00  
% 3.59/1.00  fof(f47,plain,(
% 3.59/1.00    ( ! [X0] : (sP1(X0) | ~l1_orders_2(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f16])).
% 3.59/1.00  
% 3.59/1.00  fof(f17,plain,(
% 3.59/1.00    ! [X0] : (((v2_lattice3(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_lattice3(X0))) | ~sP1(X0))),
% 3.59/1.00    inference(nnf_transformation,[],[f15])).
% 3.59/1.00  
% 3.59/1.00  fof(f35,plain,(
% 3.59/1.00    ( ! [X0] : (sP0(X0) | ~v2_lattice3(X0) | ~sP1(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f17])).
% 3.59/1.00  
% 3.59/1.00  fof(f51,plain,(
% 3.59/1.00    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f29])).
% 3.59/1.00  
% 3.59/1.00  fof(f38,plain,(
% 3.59/1.00    ( ! [X6,X0,X5] : (r1_orders_2(X0,sK5(X0,X5,X6),X5) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f24])).
% 3.59/1.00  
% 3.59/1.00  fof(f39,plain,(
% 3.59/1.00    ( ! [X6,X0,X5] : (r1_orders_2(X0,sK5(X0,X5,X6),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f24])).
% 3.59/1.00  
% 3.59/1.00  fof(f49,plain,(
% 3.59/1.00    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f29])).
% 3.59/1.00  
% 3.59/1.00  fof(f62,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(equality_resolution,[],[f49])).
% 3.59/1.00  
% 3.59/1.00  fof(f60,plain,(
% 3.59/1.00    k11_lattice3(sK7,sK8,sK9) != k11_lattice3(sK7,sK9,sK8)),
% 3.59/1.00    inference(cnf_transformation,[],[f33])).
% 3.59/1.00  
% 3.59/1.00  cnf(c_23,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2408,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2769,plain,
% 3.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2408]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_22,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2409,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2768,plain,
% 3.59/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_12,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.59/1.00      | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
% 3.59/1.00      | ~ sP0(X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2411,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 3.59/1.00      | m1_subset_1(sK5(X0_46,X1_47,X0_47),u1_struct_0(X0_46))
% 3.59/1.00      | ~ sP0(X0_46) ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2767,plain,
% 3.59/1.00      ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(X0_46,X0_47,X1_47),u1_struct_0(X0_46)) = iProver_top
% 3.59/1.00      | sP0(X0_46) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_16,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | r1_orders_2(X0,sK6(X0,X3,X2,X1),X3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_0,plain,
% 3.59/1.00      ( ~ l1_orders_2(X0) | ~ v2_lattice3(X0) | ~ v2_struct_0(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_171,plain,
% 3.59/1.00      ( ~ v2_lattice3(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | r1_orders_2(X0,sK6(X0,X3,X2,X1),X3)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_16,c_0]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_172,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | r1_orders_2(X0,sK6(X0,X3,X2,X1),X3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_171]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_26,negated_conjecture,
% 3.59/1.00      ( v5_orders_2(sK7) ),
% 3.59/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_419,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | r1_orders_2(X0,sK6(X0,X3,X2,X1),X3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1
% 3.59/1.00      | sK7 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_172,c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_420,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | ~ l1_orders_2(sK7)
% 3.59/1.00      | ~ v2_lattice3(sK7)
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_419]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_25,negated_conjecture,
% 3.59/1.00      ( v2_lattice3(sK7) ),
% 3.59/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_24,negated_conjecture,
% 3.59/1.00      ( l1_orders_2(sK7) ),
% 3.59/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_422,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_420,c_25,c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_423,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X1)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_422]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2405,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0_47,X1_47)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0_47,X2_47)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X1_47,X2_47,X0_47),X1_47)
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1_47,X2_47) = X0_47 ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_423]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2772,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = X2_47
% 3.59/1.00      | r1_orders_2(sK7,X2_47,X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,X2_47,X1_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,X2_47),X0_47) = iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2405]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_15,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | r1_orders_2(X0,sK6(X0,X3,X2,X1),X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_178,plain,
% 3.59/1.00      ( ~ v2_lattice3(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | r1_orders_2(X0,sK6(X0,X3,X2,X1),X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_15,c_0]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_179,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | r1_orders_2(X0,sK6(X0,X3,X2,X1),X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_178]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_386,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | r1_orders_2(X0,sK6(X0,X3,X2,X1),X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1
% 3.59/1.00      | sK7 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_179,c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_387,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | ~ l1_orders_2(sK7)
% 3.59/1.00      | ~ v2_lattice3(sK7)
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_386]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_391,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_387,c_25,c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_392,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X2)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_391]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2406,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0_47,X1_47)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0_47,X2_47)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X1_47,X2_47,X0_47),X2_47)
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1_47,X2_47) = X0_47 ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_392]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2771,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = X2_47
% 3.59/1.00      | r1_orders_2(sK7,X2_47,X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,X2_47,X1_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,X2_47),X1_47) = iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2406]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | r1_orders_2(X0,X1,sK5(X0,X3,X2))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ sP0(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2414,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 3.59/1.00      | ~ r1_orders_2(X0_46,X0_47,X2_47)
% 3.59/1.00      | r1_orders_2(X0_46,X0_47,sK5(X0_46,X2_47,X1_47))
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 3.59/1.00      | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
% 3.59/1.00      | ~ sP0(X0_46) ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2764,plain,
% 3.59/1.00      ( r1_orders_2(X0_46,X0_47,X1_47) != iProver_top
% 3.59/1.00      | r1_orders_2(X0_46,X0_47,X2_47) != iProver_top
% 3.59/1.00      | r1_orders_2(X0_46,X0_47,sK5(X0_46,X2_47,X1_47)) = iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(X0_46)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(X0_46)) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 3.59/1.00      | sP0(X0_46) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_14,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ r1_orders_2(X0,sK6(X0,X3,X2,X1),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_183,plain,
% 3.59/1.00      ( ~ v2_lattice3(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ r1_orders_2(X0,sK6(X0,X3,X2,X1),X1)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_14,c_0]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_184,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ r1_orders_2(X0,sK6(X0,X3,X2,X1),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_183]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_353,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ r1_orders_2(X0,sK6(X0,X3,X2,X1),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1
% 3.59/1.00      | sK7 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_184,c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_354,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | ~ r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X0)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | ~ l1_orders_2(sK7)
% 3.59/1.00      | ~ v2_lattice3(sK7)
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_353]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_358,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | ~ r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X0)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_354,c_25,c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_359,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | ~ r1_orders_2(sK7,sK6(sK7,X1,X2,X0),X0)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_358]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2407,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0_47,X1_47)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0_47,X2_47)
% 3.59/1.00      | ~ r1_orders_2(sK7,sK6(sK7,X1_47,X2_47,X0_47),X0_47)
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1_47,X2_47) = X0_47 ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_359]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2770,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = X2_47
% 3.59/1.00      | r1_orders_2(sK7,X2_47,X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,X2_47,X1_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,X2_47),X2_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2407]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4295,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X3_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X2_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X1_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2764,c_2770]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_28,plain,
% 3.59/1.00      ( v2_lattice3(sK7) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_29,plain,
% 3.59/1.00      ( l1_orders_2(sK7) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_13,plain,
% 3.59/1.00      ( sP1(X0) | ~ l1_orders_2(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_49,plain,
% 3.59/1.00      ( sP1(X0) = iProver_top | l1_orders_2(X0) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_51,plain,
% 3.59/1.00      ( sP1(sK7) = iProver_top | l1_orders_2(sK7) != iProver_top ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_49]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2,plain,
% 3.59/1.00      ( ~ sP1(X0) | sP0(X0) | ~ v2_lattice3(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_80,plain,
% 3.59/1.00      ( sP1(X0) != iProver_top
% 3.59/1.00      | sP0(X0) = iProver_top
% 3.59/1.00      | v2_lattice3(X0) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_82,plain,
% 3.59/1.00      ( sP1(sK7) != iProver_top
% 3.59/1.00      | sP0(sK7) = iProver_top
% 3.59/1.00      | v2_lattice3(sK7) != iProver_top ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_80]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_17,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | m1_subset_1(sK6(X0,X3,X2,X1),u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_164,plain,
% 3.59/1.00      ( ~ v2_lattice3(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | m1_subset_1(sK6(X0,X3,X2,X1),u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_17,c_0]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_165,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | m1_subset_1(sK6(X0,X3,X2,X1),u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_164]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_448,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ r1_orders_2(X0,X1,X3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | m1_subset_1(sK6(X0,X3,X2,X1),u1_struct_0(X0))
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | k11_lattice3(X0,X3,X2) = X1
% 3.59/1.00      | sK7 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_165,c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_449,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | m1_subset_1(sK6(sK7,X1,X2,X0),u1_struct_0(sK7))
% 3.59/1.00      | ~ l1_orders_2(sK7)
% 3.59/1.00      | ~ v2_lattice3(sK7)
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_448]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_453,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | m1_subset_1(sK6(sK7,X1,X2,X0),u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_449,c_25,c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_454,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0,X1)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0,X2)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | m1_subset_1(sK6(sK7,X1,X2,X0),u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1,X2) = X0 ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_453]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2404,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,X0_47,X1_47)
% 3.59/1.00      | ~ r1_orders_2(sK7,X0_47,X2_47)
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.59/1.00      | m1_subset_1(sK6(sK7,X1_47,X2_47,X0_47),u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X1_47,X2_47) = X0_47 ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_454]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4052,plain,
% 3.59/1.00      ( ~ r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X2_47)
% 3.59/1.00      | ~ r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X3_47)
% 3.59/1.00      | ~ m1_subset_1(X2_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X3_47,u1_struct_0(sK7))
% 3.59/1.00      | m1_subset_1(sK6(sK7,X2_47,X3_47,sK5(sK7,X0_47,X1_47)),u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7))
% 3.59/1.00      | k11_lattice3(sK7,X2_47,X3_47) = sK5(sK7,X0_47,X1_47) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_2404]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4058,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X1_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),u1_struct_0(sK7)) = iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_4052]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4464,plain,
% 3.59/1.00      ( m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X3_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X2_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X1_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_4295,c_28,c_29,c_51,c_82,c_4058]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4465,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X3_47)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X3_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X3_47)),X2_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X3_47),X1_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X3_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,X2_47,X3_47),u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_4464]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4481,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X1_47)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X1_47)),X2_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X1_47),X1_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X1_47),X0_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,X2_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2771,c_4465]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4561,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X1_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2772,c_4481]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_11,plain,
% 3.59/1.00      ( r1_orders_2(X0,sK5(X0,X1,X2),X1)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ sP0(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2412,plain,
% 3.59/1.00      ( r1_orders_2(X0_46,sK5(X0_46,X0_47,X1_47),X0_47)
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 3.59/1.00      | ~ sP0(X0_46) ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3014,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X0_47)
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ sP0(sK7) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_2412]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3020,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X0_47) = iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3014]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_10,plain,
% 3.59/1.00      ( r1_orders_2(X0,sK5(X0,X1,X2),X2)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ sP0(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2413,plain,
% 3.59/1.00      ( r1_orders_2(X0_46,sK5(X0_46,X0_47,X1_47),X1_47)
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 3.59/1.00      | ~ sP0(X0_46) ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3040,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X1_47)
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ sP0(sK7) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_2413]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3046,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,X0_47,X1_47),X1_47) = iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3040]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4813,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_4561,c_28,c_29,c_51,c_82,c_3020,c_3046]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4823,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2767,c_4813]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5370,plain,
% 3.59/1.00      ( m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47) ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_4823,c_28,c_29,c_51,c_82]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5371,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X0_47,X1_47)
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_5370]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5379,plain,
% 3.59/1.00      ( k11_lattice3(sK7,sK9,X0_47) = sK5(sK7,sK9,X0_47)
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2768,c_5371]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5482,plain,
% 3.59/1.00      ( k11_lattice3(sK7,sK9,sK8) = sK5(sK7,sK9,sK8) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2769,c_5379]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_19,plain,
% 3.59/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | v2_struct_0(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_152,plain,
% 3.59/1.00      ( ~ v2_lattice3(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_19,c_0]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_153,plain,
% 3.59/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0) ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_152]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_514,plain,
% 3.59/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | ~ v2_lattice3(X0)
% 3.59/1.00      | sK7 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_153,c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_515,plain,
% 3.59/1.00      ( r1_orders_2(sK7,k11_lattice3(sK7,X0,X1),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(k11_lattice3(sK7,X0,X1),u1_struct_0(sK7))
% 3.59/1.00      | ~ l1_orders_2(sK7)
% 3.59/1.00      | ~ v2_lattice3(sK7) ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_514]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_519,plain,
% 3.59/1.00      ( r1_orders_2(sK7,k11_lattice3(sK7,X0,X1),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(k11_lattice3(sK7,X0,X1),u1_struct_0(sK7)) ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_515,c_25,c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2402,plain,
% 3.59/1.00      ( r1_orders_2(sK7,k11_lattice3(sK7,X0_47,X1_47),X1_47)
% 3.59/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(k11_lattice3(sK7,X0_47,X1_47),u1_struct_0(sK7)) ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_519]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2775,plain,
% 3.59/1.00      ( r1_orders_2(sK7,k11_lattice3(sK7,X0_47,X1_47),X1_47) = iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(k11_lattice3(sK7,X0_47,X1_47),u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2402]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5607,plain,
% 3.59/1.00      ( r1_orders_2(sK7,k11_lattice3(sK7,sK9,sK8),sK8) = iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_5482,c_2775]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5628,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK8) = iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(light_normalisation,[status(thm)],[c_5607,c_5482]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_30,plain,
% 3.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_31,plain,
% 3.59/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4015,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK8)
% 3.59/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7))
% 3.59/1.00      | ~ sP0(sK7) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_3040]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4018,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK8) = iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_4015]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6288,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK8) = iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_5628,c_28,c_29,c_30,c_31,c_51,c_82,c_4018]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4482,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X2_47,X0_47)
% 3.59/1.00      | r1_orders_2(sK7,sK6(sK7,X0_47,X1_47,sK5(sK7,X2_47,X0_47)),X2_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X0_47),X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X2_47,X0_47),X1_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X2_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,X2_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2772,c_4465]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4966,plain,
% 3.59/1.00      ( k11_lattice3(sK7,X0_47,X1_47) = sK5(sK7,X1_47,X0_47)
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X1_47,X0_47),X0_47) != iProver_top
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,X1_47,X0_47),X1_47) != iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(X1_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,X1_47,X0_47),u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2771,c_4482]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6295,plain,
% 3.59/1.00      ( k11_lattice3(sK7,sK8,sK9) = sK5(sK7,sK9,sK8)
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK9) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_6288,c_4966]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5380,plain,
% 3.59/1.00      ( k11_lattice3(sK7,sK8,X0_47) = sK5(sK7,sK8,X0_47)
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2769,c_5371]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5778,plain,
% 3.59/1.00      ( k11_lattice3(sK7,sK8,sK9) = sK5(sK7,sK8,sK9) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2768,c_5380]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6301,plain,
% 3.59/1.00      ( sK5(sK7,sK8,sK9) = sK5(sK7,sK9,sK8)
% 3.59/1.00      | r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK9) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
% 3.59/1.00      inference(light_normalisation,[status(thm)],[c_6295,c_5778]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_21,negated_conjecture,
% 3.59/1.00      ( k11_lattice3(sK7,sK8,sK9) != k11_lattice3(sK7,sK9,sK8) ),
% 3.59/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2410,negated_conjecture,
% 3.59/1.00      ( k11_lattice3(sK7,sK8,sK9) != k11_lattice3(sK7,sK9,sK8) ),
% 3.59/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5605,plain,
% 3.59/1.00      ( k11_lattice3(sK7,sK8,sK9) != sK5(sK7,sK9,sK8) ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_5482,c_2410]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5816,plain,
% 3.59/1.00      ( sK5(sK7,sK8,sK9) != sK5(sK7,sK9,sK8) ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_5778,c_5605]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5146,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | m1_subset_1(sK5(sK7,sK9,X0_47),u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.59/1.00      | ~ sP0(sK7) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_2411]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5147,plain,
% 3.59/1.00      ( m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK5(sK7,sK9,X0_47),u1_struct_0(sK7)) = iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_5146]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5149,plain,
% 3.59/1.00      ( m1_subset_1(sK5(sK7,sK9,sK8),u1_struct_0(sK7)) = iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_5147]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3371,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,sK9,X0_47),sK9)
% 3.59/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK7))
% 3.59/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.59/1.00      | ~ sP0(sK7) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_3014]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3372,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,sK9,X0_47),sK9) = iProver_top
% 3.59/1.00      | m1_subset_1(X0_47,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3371]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3374,plain,
% 3.59/1.00      ( r1_orders_2(sK7,sK5(sK7,sK9,sK8),sK9) = iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 3.59/1.00      | sP0(sK7) != iProver_top ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_3372]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(contradiction,plain,
% 3.59/1.00      ( $false ),
% 3.59/1.00      inference(minisat,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_6301,c_5816,c_5149,c_3374,c_82,c_51,c_31,c_30,c_29,
% 3.59/1.00                 c_28]) ).
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  ------                               Statistics
% 3.59/1.00  
% 3.59/1.00  ------ General
% 3.59/1.00  
% 3.59/1.00  abstr_ref_over_cycles:                  0
% 3.59/1.00  abstr_ref_under_cycles:                 0
% 3.59/1.00  gc_basic_clause_elim:                   0
% 3.59/1.00  forced_gc_time:                         0
% 3.59/1.00  parsing_time:                           0.01
% 3.59/1.00  unif_index_cands_time:                  0.
% 3.59/1.00  unif_index_add_time:                    0.
% 3.59/1.00  orderings_time:                         0.
% 3.59/1.00  out_proof_time:                         0.026
% 3.59/1.00  total_time:                             0.27
% 3.59/1.00  num_of_symbols:                         49
% 3.59/1.00  num_of_terms:                           5153
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing
% 3.59/1.00  
% 3.59/1.00  num_of_splits:                          0
% 3.59/1.00  num_of_split_atoms:                     0
% 3.59/1.00  num_of_reused_defs:                     0
% 3.59/1.00  num_eq_ax_congr_red:                    41
% 3.59/1.00  num_of_sem_filtered_clauses:            2
% 3.59/1.00  num_of_subtypes:                        3
% 3.59/1.00  monotx_restored_types:                  0
% 3.59/1.00  sat_num_of_epr_types:                   0
% 3.59/1.00  sat_num_of_non_cyclic_types:            0
% 3.59/1.00  sat_guarded_non_collapsed_types:        1
% 3.59/1.00  num_pure_diseq_elim:                    0
% 3.59/1.00  simp_replaced_by:                       0
% 3.59/1.00  res_preprocessed:                       101
% 3.59/1.00  prep_upred:                             0
% 3.59/1.00  prep_unflattend:                        29
% 3.59/1.00  smt_new_axioms:                         0
% 3.59/1.00  pred_elim_cands:                        3
% 3.59/1.00  pred_elim:                              4
% 3.59/1.00  pred_elim_cl:                           5
% 3.59/1.00  pred_elim_cycles:                       6
% 3.59/1.00  merged_defs:                            0
% 3.59/1.00  merged_defs_ncl:                        0
% 3.59/1.00  bin_hyper_res:                          0
% 3.59/1.00  prep_cycles:                            4
% 3.59/1.00  pred_elim_time:                         0.035
% 3.59/1.00  splitting_time:                         0.
% 3.59/1.00  sem_filter_time:                        0.
% 3.59/1.00  monotx_time:                            0.
% 3.59/1.00  subtype_inf_time:                       0.
% 3.59/1.00  
% 3.59/1.00  ------ Problem properties
% 3.59/1.00  
% 3.59/1.00  clauses:                                21
% 3.59/1.00  conjectures:                            3
% 3.59/1.00  epr:                                    1
% 3.59/1.00  horn:                                   13
% 3.59/1.00  ground:                                 4
% 3.59/1.00  unary:                                  4
% 3.59/1.00  binary:                                 2
% 3.59/1.00  lits:                                   90
% 3.59/1.00  lits_eq:                                5
% 3.59/1.00  fd_pure:                                0
% 3.59/1.00  fd_pseudo:                              0
% 3.59/1.00  fd_cond:                                0
% 3.59/1.00  fd_pseudo_cond:                         4
% 3.59/1.00  ac_symbols:                             0
% 3.59/1.00  
% 3.59/1.00  ------ Propositional Solver
% 3.59/1.00  
% 3.59/1.00  prop_solver_calls:                      27
% 3.59/1.00  prop_fast_solver_calls:                 1655
% 3.59/1.00  smt_solver_calls:                       0
% 3.59/1.00  smt_fast_solver_calls:                  0
% 3.59/1.00  prop_num_of_clauses:                    1320
% 3.59/1.00  prop_preprocess_simplified:             4822
% 3.59/1.00  prop_fo_subsumed:                       39
% 3.59/1.00  prop_solver_time:                       0.
% 3.59/1.00  smt_solver_time:                        0.
% 3.59/1.00  smt_fast_solver_time:                   0.
% 3.59/1.00  prop_fast_solver_time:                  0.
% 3.59/1.00  prop_unsat_core_time:                   0.
% 3.59/1.00  
% 3.59/1.00  ------ QBF
% 3.59/1.00  
% 3.59/1.00  qbf_q_res:                              0
% 3.59/1.00  qbf_num_tautologies:                    0
% 3.59/1.00  qbf_prep_cycles:                        0
% 3.59/1.00  
% 3.59/1.00  ------ BMC1
% 3.59/1.00  
% 3.59/1.00  bmc1_current_bound:                     -1
% 3.59/1.00  bmc1_last_solved_bound:                 -1
% 3.59/1.00  bmc1_unsat_core_size:                   -1
% 3.59/1.00  bmc1_unsat_core_parents_size:           -1
% 3.59/1.00  bmc1_merge_next_fun:                    0
% 3.59/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation
% 3.59/1.00  
% 3.59/1.00  inst_num_of_clauses:                    349
% 3.59/1.00  inst_num_in_passive:                    31
% 3.59/1.00  inst_num_in_active:                     204
% 3.59/1.00  inst_num_in_unprocessed:                114
% 3.59/1.00  inst_num_of_loops:                      240
% 3.59/1.00  inst_num_of_learning_restarts:          0
% 3.59/1.00  inst_num_moves_active_passive:          33
% 3.59/1.00  inst_lit_activity:                      0
% 3.59/1.00  inst_lit_activity_moves:                0
% 3.59/1.00  inst_num_tautologies:                   0
% 3.59/1.00  inst_num_prop_implied:                  0
% 3.59/1.00  inst_num_existing_simplified:           0
% 3.59/1.00  inst_num_eq_res_simplified:             0
% 3.59/1.00  inst_num_child_elim:                    0
% 3.59/1.00  inst_num_of_dismatching_blockings:      340
% 3.59/1.00  inst_num_of_non_proper_insts:           559
% 3.59/1.00  inst_num_of_duplicates:                 0
% 3.59/1.00  inst_inst_num_from_inst_to_res:         0
% 3.59/1.00  inst_dismatching_checking_time:         0.
% 3.59/1.00  
% 3.59/1.00  ------ Resolution
% 3.59/1.00  
% 3.59/1.00  res_num_of_clauses:                     0
% 3.59/1.00  res_num_in_passive:                     0
% 3.59/1.00  res_num_in_active:                      0
% 3.59/1.00  res_num_of_loops:                       105
% 3.59/1.00  res_forward_subset_subsumed:            22
% 3.59/1.00  res_backward_subset_subsumed:           0
% 3.59/1.00  res_forward_subsumed:                   0
% 3.59/1.00  res_backward_subsumed:                  0
% 3.59/1.00  res_forward_subsumption_resolution:     0
% 3.59/1.00  res_backward_subsumption_resolution:    0
% 3.59/1.00  res_clause_to_clause_subsumption:       1209
% 3.59/1.00  res_orphan_elimination:                 0
% 3.59/1.00  res_tautology_del:                      15
% 3.59/1.00  res_num_eq_res_simplified:              0
% 3.59/1.00  res_num_sel_changes:                    0
% 3.59/1.00  res_moves_from_active_to_pass:          0
% 3.59/1.00  
% 3.59/1.00  ------ Superposition
% 3.59/1.00  
% 3.59/1.00  sup_time_total:                         0.
% 3.59/1.00  sup_time_generating:                    0.
% 3.59/1.00  sup_time_sim_full:                      0.
% 3.59/1.00  sup_time_sim_immed:                     0.
% 3.59/1.00  
% 3.59/1.00  sup_num_of_clauses:                     82
% 3.59/1.00  sup_num_in_active:                      44
% 3.59/1.00  sup_num_in_passive:                     38
% 3.59/1.00  sup_num_of_loops:                       46
% 3.59/1.00  sup_fw_superposition:                   49
% 3.59/1.00  sup_bw_superposition:                   37
% 3.59/1.00  sup_immediate_simplified:               27
% 3.59/1.00  sup_given_eliminated:                   0
% 3.59/1.00  comparisons_done:                       0
% 3.59/1.00  comparisons_avoided:                    8
% 3.59/1.00  
% 3.59/1.00  ------ Simplifications
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  sim_fw_subset_subsumed:                 15
% 3.59/1.00  sim_bw_subset_subsumed:                 1
% 3.59/1.00  sim_fw_subsumed:                        0
% 3.59/1.00  sim_bw_subsumed:                        1
% 3.59/1.00  sim_fw_subsumption_res:                 0
% 3.59/1.00  sim_bw_subsumption_res:                 0
% 3.59/1.00  sim_tautology_del:                      1
% 3.59/1.00  sim_eq_tautology_del:                   0
% 3.59/1.00  sim_eq_res_simp:                        0
% 3.59/1.00  sim_fw_demodulated:                     0
% 3.59/1.00  sim_bw_demodulated:                     2
% 3.59/1.00  sim_light_normalised:                   11
% 3.59/1.00  sim_joinable_taut:                      0
% 3.59/1.00  sim_joinable_simp:                      0
% 3.59/1.00  sim_ac_normalised:                      0
% 3.59/1.00  sim_smt_subsumption:                    0
% 3.59/1.00  
%------------------------------------------------------------------------------
