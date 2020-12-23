%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1569+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:55 EST 2020

% Result     : Theorem 1.26s
% Output     : CNFRefutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  146 (2141 expanded)
%              Number of clauses        :  104 ( 676 expanded)
%              Number of leaves         :   10 ( 453 expanded)
%              Depth                    :   26
%              Number of atoms          :  669 (14918 expanded)
%              Number of equality atoms :  169 (2265 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK1(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK1(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK1(X0,X1,X2))
          | r2_lattice3(X0,X1,sK1(X0,X1,X2)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK1(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK1(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK1(X0,X1,X2))
              | r2_lattice3(X0,X1,sK1(X0,X1,X2)) )
            & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK1(X0,X1,X2))
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                  <=> r2_lattice3(X0,X2,X3) ) )
              & r1_yellow_0(X0,X1) )
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <=> r2_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <=> r2_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r2_lattice3(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r2_lattice3(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
     => ( k1_yellow_0(X0,sK3) != k1_yellow_0(X0,sK4)
        & ! [X3] :
            ( ( ( r2_lattice3(X0,sK3,X3)
                | ~ r2_lattice3(X0,sK4,X3) )
              & ( r2_lattice3(X0,sK4,X3)
                | ~ r2_lattice3(X0,sK3,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_yellow_0(X0,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
            & ! [X3] :
                ( ( ( r2_lattice3(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3) )
                  & ( r2_lattice3(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( k1_yellow_0(sK2,X1) != k1_yellow_0(sK2,X2)
          & ! [X3] :
              ( ( ( r2_lattice3(sK2,X1,X3)
                  | ~ r2_lattice3(sK2,X2,X3) )
                & ( r2_lattice3(sK2,X2,X3)
                  | ~ r2_lattice3(sK2,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
          & r1_yellow_0(sK2,X1) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_yellow_0(sK2,sK3) != k1_yellow_0(sK2,sK4)
    & ! [X3] :
        ( ( ( r2_lattice3(sK2,sK3,X3)
            | ~ r2_lattice3(sK2,sK4,X3) )
          & ( r2_lattice3(sK2,sK4,X3)
            | ~ r2_lattice3(sK2,sK3,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
    & r1_yellow_0(sK2,sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f24,f23])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X3] :
      ( r2_lattice3(sK2,sK3,X3)
      | ~ r2_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    r1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    k1_yellow_0(sK2,sK3) != k1_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_lattice3(X0,X1,sK0(X0,X1,X2))
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,plain,
    ( r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | r2_lattice3(X0,X2,sK1(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_224,plain,
    ( r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | r2_lattice3(X0,X2,sK1(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_225,plain,
    ( r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | r2_lattice3(sK2,X1,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | r1_yellow_0(sK2,X1)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_227,plain,
    ( r1_yellow_0(sK2,X1)
    | ~ r1_yellow_0(sK2,X0)
    | r2_lattice3(sK2,X1,sK1(sK2,X0,X1))
    | r2_lattice3(sK2,X0,sK1(sK2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_225,c_13])).

cnf(c_228,plain,
    ( r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | r2_lattice3(sK2,X1,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | r1_yellow_0(sK2,X1) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_567,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,X1_42))
    | r2_lattice3(sK2,X1_42,sK1(sK2,X0_42,X1_42))
    | ~ r1_yellow_0(sK2,X0_42)
    | r1_yellow_0(sK2,X1_42) ),
    inference(subtyping,[status(esa)],[c_228])).

cnf(c_813,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,X1_42)) = iProver_top
    | r2_lattice3(sK2,X1_42,sK1(sK2,X0_42,X1_42)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top
    | r1_yellow_0(sK2,X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_10,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK4,X0)
    | r2_lattice3(sK2,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_571,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK4,X0_43)
    | r2_lattice3(sK2,sK3,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_809,plain,
    ( r2_lattice3(sK2,sK4,X0_43) != iProver_top
    | r2_lattice3(sK2,sK3,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_1444,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,sK3,sK1(sK2,X0_42,sK4)) = iProver_top
    | m1_subset_1(sK1(sK2,X0_42,sK4),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top
    | r1_yellow_0(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_809])).

cnf(c_12,negated_conjecture,
    ( r1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,plain,
    ( r1_yellow_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,negated_conjecture,
    ( k1_yellow_0(sK2,sK3) != k1_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_572,negated_conjecture,
    ( k1_yellow_0(sK2,sK3) != k1_yellow_0(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_83,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_5])).

cnf(c_296,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_83,c_13])).

cnf(c_297,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0))
    | ~ r1_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_564,plain,
    ( r2_lattice3(sK2,X0_42,k1_yellow_0(sK2,X0_42))
    | ~ r1_yellow_0(sK2,X0_42) ),
    inference(subtyping,[status(esa)],[c_297])).

cnf(c_597,plain,
    ( r2_lattice3(sK2,X0_42,k1_yellow_0(sK2,X0_42)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_599,plain,
    ( r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK3)) = iProver_top
    | r1_yellow_0(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_308,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_309,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_563,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0_42),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_600,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0_42),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_602,plain,
    ( m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_11,negated_conjecture,
    ( r2_lattice3(sK2,sK4,X0)
    | ~ r2_lattice3(sK2,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_570,negated_conjecture,
    ( r2_lattice3(sK2,sK4,X0_43)
    | ~ r2_lattice3(sK2,sK3,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_931,plain,
    ( r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK3))
    | ~ r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_934,plain,
    ( r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK3)) = iProver_top
    | r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK3)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_575,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_965,plain,
    ( k1_yellow_0(sK2,sK4) != X0_43
    | k1_yellow_0(sK2,sK3) != X0_43
    | k1_yellow_0(sK2,sK3) = k1_yellow_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_1005,plain,
    ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK2,sK3)
    | k1_yellow_0(sK2,sK3) = k1_yellow_0(sK2,sK4)
    | k1_yellow_0(sK2,sK3) != k1_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_574,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1006,plain,
    ( k1_yellow_0(sK2,sK3) = k1_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_8,plain,
    ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_207,plain,
    ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X0,X2)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_208,plain,
    ( m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0)
    | r1_yellow_0(sK2,X1)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_210,plain,
    ( r1_yellow_0(sK2,X1)
    | ~ r1_yellow_0(sK2,X0)
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_208,c_13])).

cnf(c_211,plain,
    ( m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0)
    | r1_yellow_0(sK2,X1) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_568,plain,
    ( m1_subset_1(sK1(sK2,X0_42,X1_42),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42)
    | r1_yellow_0(sK2,X1_42) ),
    inference(subtyping,[status(esa)],[c_211])).

cnf(c_1054,plain,
    ( m1_subset_1(sK1(sK2,X0_42,sK4),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42)
    | r1_yellow_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_1055,plain,
    ( m1_subset_1(sK1(sK2,X0_42,sK4),u1_struct_0(sK2)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top
    | r1_yellow_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_317,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_318,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0)
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_562,plain,
    ( ~ r2_lattice3(sK2,X0_42,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_42,X0_43),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42)
    | k1_yellow_0(sK2,X0_42) = X0_43 ),
    inference(subtyping,[status(esa)],[c_318])).

cnf(c_947,plain,
    ( ~ r2_lattice3(sK2,X0_42,k1_yellow_0(sK2,X1_42))
    | m1_subset_1(sK0(sK2,X0_42,k1_yellow_0(sK2,X1_42)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X1_42),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42)
    | k1_yellow_0(sK2,X0_42) = k1_yellow_0(sK2,X1_42) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_1077,plain,
    ( ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK3))
    | m1_subset_1(sK0(sK2,sK4,k1_yellow_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,sK4)
    | k1_yellow_0(sK2,sK4) = k1_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_1078,plain,
    ( k1_yellow_0(sK2,sK4) = k1_yellow_0(sK2,sK3)
    | r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK3)) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,k1_yellow_0(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_0,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_359,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_360,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0)
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_560,plain,
    ( ~ r2_lattice3(sK2,X0_42,X0_43)
    | ~ r1_orders_2(sK2,X0_43,sK0(sK2,X0_42,X0_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42)
    | k1_yellow_0(sK2,X0_42) = X0_43 ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_955,plain,
    ( ~ r2_lattice3(sK2,X0_42,k1_yellow_0(sK2,X1_42))
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,X1_42),sK0(sK2,X0_42,k1_yellow_0(sK2,X1_42)))
    | ~ m1_subset_1(k1_yellow_0(sK2,X1_42),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42)
    | k1_yellow_0(sK2,X0_42) = k1_yellow_0(sK2,X1_42) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1100,plain,
    ( ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK3))
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK3),sK0(sK2,sK4,k1_yellow_0(sK2,sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,sK4)
    | k1_yellow_0(sK2,sK4) = k1_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_1101,plain,
    ( k1_yellow_0(sK2,sK4) = k1_yellow_0(sK2,sK3)
    | r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK3)) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK3),sK0(sK2,sK4,k1_yellow_0(sK2,sK3))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1100])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_338,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_339,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X0,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0)
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_561,plain,
    ( ~ r2_lattice3(sK2,X0_42,X0_43)
    | r2_lattice3(sK2,X0_42,sK0(sK2,X0_42,X0_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42)
    | k1_yellow_0(sK2,X0_42) = X0_43 ),
    inference(subtyping,[status(esa)],[c_339])).

cnf(c_960,plain,
    ( r2_lattice3(sK2,X0_42,sK0(sK2,X0_42,k1_yellow_0(sK2,X1_42)))
    | ~ r2_lattice3(sK2,X0_42,k1_yellow_0(sK2,X1_42))
    | ~ m1_subset_1(k1_yellow_0(sK2,X1_42),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42)
    | k1_yellow_0(sK2,X0_42) = k1_yellow_0(sK2,X1_42) ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_1116,plain,
    ( r2_lattice3(sK2,sK4,sK0(sK2,sK4,k1_yellow_0(sK2,sK3)))
    | ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,sK4)
    | k1_yellow_0(sK2,sK4) = k1_yellow_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_1117,plain,
    ( k1_yellow_0(sK2,sK4) = k1_yellow_0(sK2,sK3)
    | r2_lattice3(sK2,sK4,sK0(sK2,sK4,k1_yellow_0(sK2,sK3))) = iProver_top
    | r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK3)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_90,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_5])).

cnf(c_91,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_90])).

cnf(c_278,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_91,c_13])).

cnf(c_279,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_565,plain,
    ( ~ r2_lattice3(sK2,X0_42,X0_43)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0_42),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42) ),
    inference(subtyping,[status(esa)],[c_279])).

cnf(c_1366,plain,
    ( ~ r2_lattice3(sK2,X0_42,sK0(sK2,sK4,k1_yellow_0(sK2,sK3)))
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0_42),sK0(sK2,sK4,k1_yellow_0(sK2,sK3)))
    | ~ m1_subset_1(sK0(sK2,sK4,k1_yellow_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,X0_42) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_1367,plain,
    ( r2_lattice3(sK2,X0_42,sK0(sK2,sK4,k1_yellow_0(sK2,sK3))) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0_42),sK0(sK2,sK4,k1_yellow_0(sK2,sK3))) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,k1_yellow_0(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1366])).

cnf(c_1369,plain,
    ( r2_lattice3(sK2,sK3,sK0(sK2,sK4,k1_yellow_0(sK2,sK3))) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK3),sK0(sK2,sK4,k1_yellow_0(sK2,sK3))) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,k1_yellow_0(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_1388,plain,
    ( ~ r2_lattice3(sK2,sK4,sK0(sK2,sK4,k1_yellow_0(sK2,sK3)))
    | r2_lattice3(sK2,sK3,sK0(sK2,sK4,k1_yellow_0(sK2,sK3)))
    | ~ m1_subset_1(sK0(sK2,sK4,k1_yellow_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_1389,plain,
    ( r2_lattice3(sK2,sK4,sK0(sK2,sK4,k1_yellow_0(sK2,sK3))) != iProver_top
    | r2_lattice3(sK2,sK3,sK0(sK2,sK4,k1_yellow_0(sK2,sK3))) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,k1_yellow_0(sK2,sK3)),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_1573,plain,
    ( r2_lattice3(sK2,sK3,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top
    | r1_yellow_0(sK2,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1444,c_17,c_572,c_599,c_602,c_934,c_1005,c_1006,c_1055,c_1078,c_1101,c_1117,c_1369,c_1389])).

cnf(c_1574,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,sK3,sK1(sK2,X0_42,sK4)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top
    | r1_yellow_0(sK2,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1573])).

cnf(c_1579,plain,
    ( r1_yellow_0(sK2,X0_42) != iProver_top
    | r2_lattice3(sK2,sK3,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1574,c_17,c_572,c_599,c_602,c_934,c_1005,c_1006,c_1078,c_1101,c_1117,c_1369,c_1389])).

cnf(c_1580,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,sK3,sK1(sK2,X0_42,sK4)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_1579])).

cnf(c_810,plain,
    ( r2_lattice3(sK2,sK4,X0_43) = iProver_top
    | r2_lattice3(sK2,sK3,X0_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_1589,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,sK4,sK1(sK2,X0_42,sK4)) = iProver_top
    | m1_subset_1(sK1(sK2,X0_42,sK4),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1580,c_810])).

cnf(c_1052,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4))
    | r2_lattice3(sK2,sK4,sK1(sK2,X0_42,sK4))
    | ~ r1_yellow_0(sK2,X0_42)
    | r1_yellow_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_1063,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,sK4,sK1(sK2,X0_42,sK4)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top
    | r1_yellow_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_1591,plain,
    ( r2_lattice3(sK2,sK3,sK1(sK2,sK4,sK4)) = iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK4),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1580,c_809])).

cnf(c_1629,plain,
    ( r1_yellow_0(sK2,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1591,c_17,c_572,c_599,c_602,c_934,c_1005,c_1006,c_1078,c_1101,c_1117,c_1369,c_1389])).

cnf(c_1674,plain,
    ( r2_lattice3(sK2,sK4,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1589,c_17,c_572,c_599,c_602,c_934,c_1005,c_1006,c_1063,c_1078,c_1101,c_1117,c_1369,c_1389])).

cnf(c_1675,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) = iProver_top
    | r2_lattice3(sK2,sK4,sK1(sK2,X0_42,sK4)) = iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_1674])).

cnf(c_1685,plain,
    ( r2_lattice3(sK2,sK4,sK1(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_810])).

cnf(c_1582,plain,
    ( r2_lattice3(sK2,sK3,sK1(sK2,sK3,sK4)) = iProver_top
    | r1_yellow_0(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_6,plain,
    ( ~ r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK1(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_244,plain,
    ( ~ r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK1(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_245,plain,
    ( ~ r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | ~ r2_lattice3(sK2,X1,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | r1_yellow_0(sK2,X1)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_247,plain,
    ( r1_yellow_0(sK2,X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ r2_lattice3(sK2,X1,sK1(sK2,X0,X1))
    | ~ r2_lattice3(sK2,X0,sK1(sK2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_245,c_13])).

cnf(c_248,plain,
    ( ~ r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | ~ r2_lattice3(sK2,X1,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | r1_yellow_0(sK2,X1) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_566,plain,
    ( ~ r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,X1_42))
    | ~ r2_lattice3(sK2,X1_42,sK1(sK2,X0_42,X1_42))
    | ~ r1_yellow_0(sK2,X0_42)
    | r1_yellow_0(sK2,X1_42) ),
    inference(subtyping,[status(esa)],[c_248])).

cnf(c_1053,plain,
    ( ~ r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4))
    | ~ r2_lattice3(sK2,sK4,sK1(sK2,X0_42,sK4))
    | ~ r1_yellow_0(sK2,X0_42)
    | r1_yellow_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_1059,plain,
    ( r2_lattice3(sK2,X0_42,sK1(sK2,X0_42,sK4)) != iProver_top
    | r2_lattice3(sK2,sK4,sK1(sK2,X0_42,sK4)) != iProver_top
    | r1_yellow_0(sK2,X0_42) != iProver_top
    | r1_yellow_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_1061,plain,
    ( r2_lattice3(sK2,sK4,sK1(sK2,sK3,sK4)) != iProver_top
    | r2_lattice3(sK2,sK3,sK1(sK2,sK3,sK4)) != iProver_top
    | r1_yellow_0(sK2,sK4) = iProver_top
    | r1_yellow_0(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_1057,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | r1_yellow_0(sK2,sK4) = iProver_top
    | r1_yellow_0(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1685,c_1629,c_1582,c_1061,c_1057,c_17])).


%------------------------------------------------------------------------------
