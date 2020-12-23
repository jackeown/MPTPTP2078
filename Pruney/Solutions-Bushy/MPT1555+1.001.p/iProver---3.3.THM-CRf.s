%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1555+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:52 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 802 expanded)
%              Number of clauses        :   82 ( 162 expanded)
%              Number of leaves         :   12 ( 241 expanded)
%              Depth                    :   22
%              Number of atoms          :  657 (9176 expanded)
%              Number of equality atoms :  157 (1321 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X2,X3)
                     => r1_orders_2(X0,X3,X1) ) )
                & r1_lattice3(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( k2_yellow_0(X0,X2) = X1
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1)
                | k2_yellow_0(X0,X2) != X1 )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | ~ r1_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1)
                | k2_yellow_0(X0,X2) != X1 )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | ~ r1_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1)
                | k2_yellow_0(X0,X2) != X1 )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f16])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4,X1)
        & r1_lattice3(X0,X2,sK4)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_orders_2(X0,X3,X1)
                & r1_lattice3(X0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X2,X1)
            | k2_yellow_0(X0,X2) != X1 )
          & ( ( ! [X4] :
                  ( r1_orders_2(X0,X4,X1)
                  | ~ r1_lattice3(X0,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r1_lattice3(X0,X2,X1) )
            | k2_yellow_0(X0,X2) = X1 ) )
     => ( ( ? [X3] :
              ( ~ r1_orders_2(X0,X3,X1)
              & r1_lattice3(X0,sK3,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_lattice3(X0,sK3,X1)
          | k2_yellow_0(X0,sK3) != X1 )
        & ( ( ! [X4] :
                ( r1_orders_2(X0,X4,X1)
                | ~ r1_lattice3(X0,sK3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_lattice3(X0,sK3,X1) )
          | k2_yellow_0(X0,sK3) = X1 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1)
                | k2_yellow_0(X0,X2) != X1 )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_orders_2(X0,X3,sK2)
                  & r1_lattice3(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X2,sK2)
              | k2_yellow_0(X0,X2) != sK2 )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,sK2)
                    | ~ r1_lattice3(X0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,sK2) )
              | k2_yellow_0(X0,X2) = sK2 ) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & r1_lattice3(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X2,X1)
                  | k2_yellow_0(X0,X2) != X1 )
                & ( ( ! [X4] :
                        ( r1_orders_2(X0,X4,X1)
                        | ~ r1_lattice3(X0,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_lattice3(X0,X2,X1) )
                  | k2_yellow_0(X0,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(sK1,X3,X1)
                    & r1_lattice3(sK1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK1)) )
                | ~ r1_lattice3(sK1,X2,X1)
                | k2_yellow_0(sK1,X2) != X1 )
              & ( ( ! [X4] :
                      ( r1_orders_2(sK1,X4,X1)
                      | ~ r1_lattice3(sK1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
                  & r1_lattice3(sK1,X2,X1) )
                | k2_yellow_0(sK1,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v3_lattice3(sK1)
      & v5_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ( ~ r1_orders_2(sK1,sK4,sK2)
        & r1_lattice3(sK1,sK3,sK4)
        & m1_subset_1(sK4,u1_struct_0(sK1)) )
      | ~ r1_lattice3(sK1,sK3,sK2)
      | k2_yellow_0(sK1,sK3) != sK2 )
    & ( ( ! [X4] :
            ( r1_orders_2(sK1,X4,sK2)
            | ~ r1_lattice3(sK1,sK3,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
        & r1_lattice3(sK1,sK3,sK2) )
      | k2_yellow_0(sK1,sK3) = sK2 )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v3_lattice3(sK1)
    & v5_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f21,f20,f19,f18])).

fof(f39,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK3,sK2)
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,
    ( r1_lattice3(sK1,sK3,sK4)
    | ~ r1_lattice3(sK1,sK3,sK2)
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_lattice3(sK1,sK3,sK2)
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK0(X0,X1,X2))
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f35,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : r2_yellow_0(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    v3_lattice3(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,
    ( r1_lattice3(sK1,sK3,sK2)
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | r1_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X4] :
      ( r1_orders_2(sK1,X4,sK2)
      | ~ r1_lattice3(sK1,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | k2_yellow_0(sK1,sK3) = sK2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f24])).

cnf(c_544,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_901,plain,
    ( X0_45 != X1_45
    | X0_45 = k2_yellow_0(sK1,X0_44)
    | k2_yellow_0(sK1,X0_44) != X1_45 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_902,plain,
    ( k2_yellow_0(sK1,sK3) != sK2
    | sK2 = k2_yellow_0(sK1,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_11,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK3,sK2)
    | m1_subset_1(sK4,u1_struct_0(sK1))
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_538,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK3,sK2)
    | m1_subset_1(sK4,u1_struct_0(sK1))
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_748,plain,
    ( k2_yellow_0(sK1,sK3) != sK2
    | r1_lattice3(sK1,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK3,sK2)
    | r1_lattice3(sK1,sK3,sK4)
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_539,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK3,sK2)
    | r1_lattice3(sK1,sK3,sK4)
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_553,plain,
    ( k2_yellow_0(sK1,sK3) != sK2
    | r1_lattice3(sK1,sK3,sK2) != iProver_top
    | r1_lattice3(sK1,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_9,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK3,sK2)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_239,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_240,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | r1_orders_2(sK1,X1,k2_yellow_0(sK1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1))
    | ~ r2_yellow_0(sK1,X0)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_0,plain,
    ( r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_16,negated_conjecture,
    ( v3_lattice3(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_204,plain,
    ( r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_205,plain,
    ( r2_yellow_0(sK1,X0)
    | v2_struct_0(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_244,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | r1_orders_2(sK1,X1,k2_yellow_0(sK1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_240,c_18,c_17,c_15,c_205])).

cnf(c_366,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | ~ r1_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0) != sK2
    | k2_yellow_0(sK1,sK3) != sK2
    | sK4 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_244])).

cnf(c_367,plain,
    ( ~ r1_lattice3(sK1,X0,sK4)
    | ~ r1_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0) != sK2
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_371,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK3,sK2)
    | ~ r1_lattice3(sK1,X0,sK4)
    | k2_yellow_0(sK1,X0) != sK2
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_11])).

cnf(c_372,plain,
    ( ~ r1_lattice3(sK1,X0,sK4)
    | ~ r1_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0) != sK2
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_532,plain,
    ( ~ r1_lattice3(sK1,X0_44,sK4)
    | ~ r1_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(k2_yellow_0(sK1,X0_44),u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0_44) != sK2
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_541,plain,
    ( ~ r1_lattice3(sK1,sK3,sK2)
    | sP0_iProver_split
    | k2_yellow_0(sK1,sK3) != sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_532])).

cnf(c_566,plain,
    ( k2_yellow_0(sK1,sK3) != sK2
    | r1_lattice3(sK1,sK3,sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_540,plain,
    ( ~ r1_lattice3(sK1,X0_44,sK4)
    | ~ m1_subset_1(k2_yellow_0(sK1,X0_44),u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0_44) != sK2
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_532])).

cnf(c_567,plain,
    ( k2_yellow_0(sK1,X0_44) != sK2
    | r1_lattice3(sK1,X0_44,sK4) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X0_44),u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_569,plain,
    ( k2_yellow_0(sK1,sK3) != sK2
    | r1_lattice3(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(k2_yellow_0(sK1,sK3),u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_13,negated_conjecture,
    ( r1_lattice3(sK1,sK3,sK2)
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_537,negated_conjecture,
    ( r1_lattice3(sK1,sK3,sK2)
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_6,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_263,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_264,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_268,plain,
    ( m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,X0,X1)
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_17])).

cnf(c_269,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_534,plain,
    ( ~ r1_lattice3(sK1,X0_44,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0_45,X0_44),u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0_44) = X0_45 ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_561,plain,
    ( ~ r1_lattice3(sK1,sK3,sK2)
    | m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_5,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_287,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_288,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | r1_lattice3(sK1,X0,sK0(sK1,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r1_lattice3(sK1,X0,sK0(sK1,X1,X0))
    | ~ r1_lattice3(sK1,X0,X1)
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_17])).

cnf(c_293,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | r1_lattice3(sK1,X0,sK0(sK1,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_533,plain,
    ( ~ r1_lattice3(sK1,X0_44,X0_45)
    | r1_lattice3(sK1,X0_44,sK0(sK1,X0_45,X0_44))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0_44) = X0_45 ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_564,plain,
    ( r1_lattice3(sK1,sK3,sK0(sK1,sK2,sK3))
    | ~ r1_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_12,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK3,X0)
    | r1_orders_2(sK1,X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_311,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_312,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | ~ r1_orders_2(sK1,sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK0(sK1,X1,X0),X1)
    | ~ r1_lattice3(sK1,X0,X1)
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_17])).

cnf(c_317,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | ~ r1_orders_2(sK1,sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0) = X1 ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_393,plain,
    ( ~ r1_lattice3(sK1,X0,X1)
    | ~ r1_lattice3(sK1,sK3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | sK0(sK1,X1,X0) != X2
    | k2_yellow_0(sK1,X0) = X1
    | k2_yellow_0(sK1,sK3) = sK2
    | sK2 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_317])).

cnf(c_394,plain,
    ( ~ r1_lattice3(sK1,X0,sK2)
    | ~ r1_lattice3(sK1,sK3,sK0(sK1,sK2,X0))
    | ~ m1_subset_1(sK0(sK1,sK2,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0) = sK2
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,X0),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK3,sK0(sK1,sK2,X0))
    | ~ r1_lattice3(sK1,X0,sK2)
    | k2_yellow_0(sK1,X0) = sK2
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_14])).

cnf(c_399,plain,
    ( ~ r1_lattice3(sK1,X0,sK2)
    | ~ r1_lattice3(sK1,sK3,sK0(sK1,sK2,X0))
    | ~ m1_subset_1(sK0(sK1,sK2,X0),u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0) = sK2
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(renaming,[status(thm)],[c_398])).

cnf(c_531,plain,
    ( ~ r1_lattice3(sK1,X0_44,sK2)
    | ~ r1_lattice3(sK1,sK3,sK0(sK1,sK2,X0_44))
    | ~ m1_subset_1(sK0(sK1,sK2,X0_44),u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0_44) = sK2
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_399])).

cnf(c_571,plain,
    ( ~ r1_lattice3(sK1,sK3,sK0(sK1,sK2,sK3))
    | ~ r1_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1))
    | k2_yellow_0(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_602,negated_conjecture,
    ( k2_yellow_0(sK1,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_14,c_561,c_564,c_571])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0_45,X0_46)
    | m1_subset_1(X1_45,X0_46)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_859,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | X0_45 != sK2 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_862,plain,
    ( m1_subset_1(k2_yellow_0(sK1,X0_44),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k2_yellow_0(sK1,X0_44) != sK2 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_863,plain,
    ( k2_yellow_0(sK1,X0_44) != sK2
    | m1_subset_1(k2_yellow_0(sK1,X0_44),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_865,plain,
    ( k2_yellow_0(sK1,sK3) != sK2
    | m1_subset_1(k2_yellow_0(sK1,sK3),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_877,plain,
    ( r1_lattice3(sK1,sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_748,c_14,c_23,c_553,c_537,c_561,c_564,c_566,c_569,c_571,c_865])).

cnf(c_546,plain,
    ( ~ r1_lattice3(X0_43,X0_44,X0_45)
    | r1_lattice3(X0_43,X0_44,X1_45)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_871,plain,
    ( r1_lattice3(sK1,X0_44,X0_45)
    | ~ r1_lattice3(sK1,X0_44,k2_yellow_0(sK1,X0_44))
    | X0_45 != k2_yellow_0(sK1,X0_44) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_872,plain,
    ( X0_45 != k2_yellow_0(sK1,X0_44)
    | r1_lattice3(sK1,X0_44,X0_45) = iProver_top
    | r1_lattice3(sK1,X0_44,k2_yellow_0(sK1,X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_874,plain,
    ( sK2 != k2_yellow_0(sK1,sK3)
    | r1_lattice3(sK1,sK3,k2_yellow_0(sK1,sK3)) != iProver_top
    | r1_lattice3(sK1,sK3,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_8,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_221,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_222,plain,
    ( r1_lattice3(sK1,X0,k2_yellow_0(sK1,X0))
    | ~ m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1))
    | ~ r2_yellow_0(sK1,X0)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_226,plain,
    ( r1_lattice3(sK1,X0,k2_yellow_0(sK1,X0))
    | ~ m1_subset_1(k2_yellow_0(sK1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_18,c_17,c_15,c_205])).

cnf(c_535,plain,
    ( r1_lattice3(sK1,X0_44,k2_yellow_0(sK1,X0_44))
    | ~ m1_subset_1(k2_yellow_0(sK1,X0_44),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_557,plain,
    ( r1_lattice3(sK1,X0_44,k2_yellow_0(sK1,X0_44)) = iProver_top
    | m1_subset_1(k2_yellow_0(sK1,X0_44),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_559,plain,
    ( r1_lattice3(sK1,sK3,k2_yellow_0(sK1,sK3)) = iProver_top
    | m1_subset_1(k2_yellow_0(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_557])).

cnf(c_543,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_552,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_902,c_877,c_874,c_865,c_602,c_559,c_552,c_23])).


%------------------------------------------------------------------------------
