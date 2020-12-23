%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1485+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:44 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 699 expanded)
%              Number of clauses        :  113 ( 200 expanded)
%              Number of leaves         :   20 ( 207 expanded)
%              Depth                    :   18
%              Number of atoms          : 1057 (4489 expanded)
%              Number of equality atoms :  196 ( 684 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X6,X2)
                                  & r1_orders_2(X0,X6,X1) )
                               => r1_orders_2(X0,X6,X5) ) )
                          & r1_orders_2(X0,X5,X2)
                          & r1_orders_2(X0,X5,X1) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( k11_lattice3(X0,X1,X2) = X5
          <=> ( ! [X6] :
                  ( r1_orders_2(X0,X6,X5)
                  | ~ r1_orders_2(X0,X6,X2)
                  | ~ r1_orders_2(X0,X6,X1)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1) ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f33])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
                    & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
                    & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
                    & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f40])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
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
             => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
               => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK6)) != X1
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k12_lattice3(X0,sK5,k13_lattice3(X0,sK5,X2)) != sK5
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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
              ( k12_lattice3(sK4,X1,k13_lattice3(sK4,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5
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

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X1)
                  & r1_orders_2(X0,X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X1)
          & r1_orders_2(X0,X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
                & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
                & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
                & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
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

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
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

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5 ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3265,plain,
    ( ~ r1_orders_2(X0_49,X0_50,X1_50)
    | r1_orders_2(X0_49,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_4934,plain,
    ( ~ r1_orders_2(sK4,X0_50,X1_50)
    | r1_orders_2(sK4,X2_50,k13_lattice3(sK4,sK5,sK6))
    | X2_50 != X0_50
    | k13_lattice3(sK4,sK5,sK6) != X1_50 ),
    inference(instantiation,[status(thm)],[c_3265])).

cnf(c_8042,plain,
    ( r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X1_50,k10_lattice3(sK4,sK5,sK6))
    | X0_50 != X1_50
    | k13_lattice3(sK4,sK5,sK6) != k10_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4934])).

cnf(c_8043,plain,
    ( X0_50 != X1_50
    | k13_lattice3(sK4,sK5,sK6) != k10_lattice3(sK4,sK5,sK6)
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) = iProver_top
    | r1_orders_2(sK4,X1_50,k10_lattice3(sK4,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8042])).

cnf(c_8045,plain,
    ( k13_lattice3(sK4,sK5,sK6) != k10_lattice3(sK4,sK5,sK6)
    | sK5 != sK5
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = iProver_top
    | r1_orders_2(sK4,sK5,k10_lattice3(sK4,sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8043])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,sK2(X0,X2,X1,X3),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_826,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK2(X0,X2,X1,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_827,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | ~ r1_orders_2(sK4,X2,X1)
    | sP0(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_29])).

cnf(c_832,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_831])).

cnf(c_3237,plain,
    ( sP0(sK4,X0_50,X1_50)
    | ~ r1_orders_2(sK4,X2_50,X1_50)
    | ~ r1_orders_2(sK4,X2_50,X0_50)
    | r1_orders_2(sK4,sK2(sK4,X1_50,X0_50,X2_50),X1_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_832])).

cnf(c_7894,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5)
    | ~ r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,sK5)
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),X0_50),sK5)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_7910,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) = iProver_top
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,sK5) != iProver_top
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),X0_50),sK5) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7894])).

cnf(c_7912,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),sK5),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7910])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,sK2(X0,X2,X1,X3),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_888,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,sK2(X0,X2,X1,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_32])).

cnf(c_889,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | ~ r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_893,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X2)
    | ~ r1_orders_2(sK4,X2,X0)
    | ~ r1_orders_2(sK4,X2,X1)
    | sP0(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_889,c_29])).

cnf(c_894,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | ~ r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_893])).

cnf(c_3235,plain,
    ( sP0(sK4,X0_50,X1_50)
    | ~ r1_orders_2(sK4,X2_50,X1_50)
    | ~ r1_orders_2(sK4,X2_50,X0_50)
    | ~ r1_orders_2(sK4,sK2(sK4,X1_50,X0_50,X2_50),X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_894])).

cnf(c_7896,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5)
    | ~ r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,sK5)
    | ~ r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),X0_50),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3235])).

cnf(c_7902,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) = iProver_top
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,sK5) != iProver_top
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),X0_50),X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7896])).

cnf(c_7904,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),sK5),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7902])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k11_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3256,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | ~ r1_orders_2(X0_49,sK1(X0_49,X0_50,X1_50,X2_50),X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k11_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4669,plain,
    ( ~ sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5)
    | ~ r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,sK5)
    | ~ r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,X0_50),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50 ),
    inference(instantiation,[status(thm)],[c_3256])).

cnf(c_4685,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50
    | sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) != iProver_top
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,sK5) != iProver_top
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,X0_50),X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4669])).

cnf(c_4687,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = sK5
    | sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,sK5),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4685])).

cnf(c_4,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k11_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3254,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | r1_orders_2(X0_49,sK1(X0_49,X0_50,X1_50,X2_50),X1_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k11_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_4671,plain,
    ( ~ sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5)
    | ~ r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,sK5)
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,X0_50),sK5)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50 ),
    inference(instantiation,[status(thm)],[c_3254])).

cnf(c_4677,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50
    | sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) != iProver_top
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,sK5) != iProver_top
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,X0_50),sK5) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4671])).

cnf(c_4679,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = sK5
    | sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,sK5),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4677])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_953,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k10_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_953])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_351,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_30])).

cnf(c_352,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_105,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_354,plain,
    ( ~ v2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_30,c_29,c_105])).

cnf(c_513,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_354])).

cnf(c_514,plain,
    ( r1_orders_2(sK4,X0,k10_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_lattice3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_31,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_518,plain,
    ( ~ m1_subset_1(k10_lattice3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_orders_2(sK4,X0,k10_lattice3(sK4,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_32,c_31,c_29])).

cnf(c_519,plain,
    ( r1_orders_2(sK4,X0,k10_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_518])).

cnf(c_972,plain,
    ( r1_orders_2(sK4,X0,k10_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_954,c_519])).

cnf(c_3232,plain,
    ( r1_orders_2(sK4,X0_50,k10_lattice3(sK4,X0_50,X1_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_972])).

cnf(c_4151,plain,
    ( r1_orders_2(sK4,sK5,k10_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3232])).

cnf(c_4154,plain,
    ( r1_orders_2(sK4,sK5,k10_lattice3(sK4,sK5,sK6)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4151])).

cnf(c_3262,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_4040,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != X0_50
    | sK5 != X0_50
    | sK5 = k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_4041,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5
    | sK5 = k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4040])).

cnf(c_3778,plain,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != X0_50
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = sK5
    | sK5 != X0_50 ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_3959,plain,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = sK5
    | sK5 != k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3778])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k11_lattice3(sK4,X0,X1) = k12_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k11_lattice3(sK4,X0,X1) = k12_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_32,c_29])).

cnf(c_3246,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | k11_lattice3(sK4,X0_50,X1_50) = k12_lattice3(sK4,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_3897,plain,
    ( ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3246])).

cnf(c_3793,plain,
    ( X0_50 != X1_50
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != X1_50
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50 ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_3806,plain,
    ( X0_50 != k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3793])).

cnf(c_3896,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3806])).

cnf(c_3234,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | m1_subset_1(k10_lattice3(sK4,X0_50,X1_50),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_954])).

cnf(c_3850,plain,
    ( m1_subset_1(k10_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3234])).

cnf(c_3851,plain,
    ( m1_subset_1(k10_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3850])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_769,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k13_lattice3(sK4,X0,X1) = k10_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_768])).

cnf(c_773,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k13_lattice3(sK4,X0,X1) = k10_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_769,c_32,c_29])).

cnf(c_3239,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | k13_lattice3(sK4,X0_50,X1_50) = k10_lattice3(sK4,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_773])).

cnf(c_3832,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k13_lattice3(sK4,sK5,sK6) = k10_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3239])).

cnf(c_3264,plain,
    ( ~ m1_subset_1(X0_50,X0_51)
    | m1_subset_1(X1_50,X0_51)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_3798,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | k13_lattice3(sK4,sK5,sK6) != X0_50 ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_3831,plain,
    ( m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(k10_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | k13_lattice3(sK4,sK5,sK6) != k10_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3798])).

cnf(c_3833,plain,
    ( k13_lattice3(sK4,sK5,sK6) != k10_lattice3(sK4,sK5,sK6)
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k10_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3831])).

cnf(c_3261,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_3817,plain,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3261])).

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
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
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
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
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

cnf(c_3244,plain,
    ( r1_orders_2(sK4,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_3257,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3244])).

cnf(c_3302,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3257])).

cnf(c_3304,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3302])).

cnf(c_3258,plain,
    ( r1_orders_2(sK4,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_3244])).

cnf(c_3299,plain,
    ( r1_orders_2(sK4,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3258])).

cnf(c_3301,plain,
    ( r1_orders_2(sK4,sK5,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3299])).

cnf(c_3259,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3244])).

cnf(c_3298,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3259])).

cnf(c_26,negated_conjecture,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3249,negated_conjecture,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3272,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3261])).

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
    inference(minisat,[status(thm)],[c_8045,c_7912,c_7904,c_4687,c_4679,c_4154,c_4041,c_3959,c_3897,c_3896,c_3851,c_3850,c_3832,c_3833,c_3831,c_3817,c_3304,c_3301,c_3298,c_3249,c_3272,c_40,c_27,c_39,c_28])).


%------------------------------------------------------------------------------
