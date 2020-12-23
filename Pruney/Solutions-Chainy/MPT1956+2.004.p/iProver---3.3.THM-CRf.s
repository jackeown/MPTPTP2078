%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:21 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 488 expanded)
%              Number of clauses        :   68 ( 115 expanded)
%              Number of leaves         :   11 ( 108 expanded)
%              Depth                    :   21
%              Number of atoms          :  531 (3186 expanded)
%              Number of equality atoms :   34 (  49 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,sK3),k2_yellow_0(X0,sK2))
          | ~ r3_orders_2(X0,k1_yellow_0(X0,sK2),k1_yellow_0(X0,sK3)) )
        & r1_tarski(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r1_orders_2(sK1,k2_yellow_0(sK1,X2),k2_yellow_0(sK1,X1))
            | ~ r3_orders_2(sK1,k1_yellow_0(sK1,X1),k1_yellow_0(sK1,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK1)
      & v3_lattice3(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1)
      & v3_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
      | ~ r3_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) )
    & r1_tarski(sK2,sK3)
    & l1_orders_2(sK1)
    & v3_lattice3(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1)
    & v3_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f33,f32])).

fof(f52,plain,(
    v3_lattice3(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,
    ( ~ r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
    | ~ r3_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_8])).

cnf(c_130,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_129])).

cnf(c_10,plain,
    ( r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( v3_lattice3(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_254,plain,
    ( r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_255,plain,
    ( r1_yellow_0(sK1,X0)
    | ~ v5_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_19,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_58,plain,
    ( ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_259,plain,
    ( r1_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_19,c_18,c_16,c_58])).

cnf(c_414,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_130,c_259])).

cnf(c_415,plain,
    ( ~ r2_lattice3(sK1,X0,X1)
    | r1_orders_2(sK1,k1_yellow_0(sK1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r1_orders_2(sK1,k1_yellow_0(sK1,X0),X1)
    | ~ r2_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_16])).

cnf(c_420,plain,
    ( ~ r2_lattice3(sK1,X0,X1)
    | r1_orders_2(sK1,k1_yellow_0(sK1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_826,plain,
    ( ~ r2_lattice3(sK1,X0_51,X0_50)
    | r1_orders_2(sK1,k1_yellow_0(sK1,X0_51),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_1104,plain,
    ( ~ r2_lattice3(sK1,X0_51,k1_yellow_0(sK1,X1_51))
    | r1_orders_2(sK1,k1_yellow_0(sK1,X0_51),k1_yellow_0(sK1,X1_51))
    | ~ m1_subset_1(k1_yellow_0(sK1,X1_51),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1174,plain,
    ( ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_7,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_122,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_8])).

cnf(c_123,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_122])).

cnf(c_435,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | X2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_123,c_259])).

cnf(c_436,plain,
    ( r2_lattice3(sK1,X0,k1_yellow_0(sK1,X0))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_440,plain,
    ( r2_lattice3(sK1,X0,k1_yellow_0(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_16])).

cnf(c_825,plain,
    ( r2_lattice3(sK1,X0_51,k1_yellow_0(sK1,X0_51)) ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_1099,plain,
    ( r2_lattice3(sK1,sK3,k1_yellow_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_306,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X3
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_307,plain,
    ( r2_lattice3(X0,sK2,X1)
    | ~ r2_lattice3(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_543,plain,
    ( r2_lattice3(X0,sK2,X1)
    | ~ r2_lattice3(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_307,c_16])).

cnf(c_544,plain,
    ( r2_lattice3(sK1,sK2,X0)
    | ~ r2_lattice3(sK1,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_821,plain,
    ( r2_lattice3(sK1,sK2,X0_50)
    | ~ r2_lattice3(sK1,sK3,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_544])).

cnf(c_1098,plain,
    ( r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ r2_lattice3(sK1,sK3,k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_570,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_571,plain,
    ( m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_819,plain,
    ( m1_subset_1(k1_yellow_0(sK1,X0_51),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_571])).

cnf(c_1095,plain,
    ( m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_11,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
    | ~ r1_tarski(X2,X1)
    | ~ r2_yellow_0(X0,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_288,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
    | ~ r2_yellow_0(X0,X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_289,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,sK3),k2_yellow_0(X0,sK2))
    | ~ r2_yellow_0(X0,sK2)
    | ~ r2_yellow_0(X0,sK3)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_558,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,sK3),k2_yellow_0(X0,sK2))
    | ~ r2_yellow_0(X0,sK2)
    | ~ r2_yellow_0(X0,sK3)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_289,c_16])).

cnf(c_559,plain,
    ( r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ r2_yellow_0(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_9,plain,
    ( r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_269,plain,
    ( r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_270,plain,
    ( r2_yellow_0(sK1,X0)
    | ~ v5_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_274,plain,
    ( r2_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_19,c_18,c_16,c_58])).

cnf(c_567,plain,
    ( r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_559,c_274,c_274])).

cnf(c_14,negated_conjecture,
    ( ~ r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
    | ~ r3_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_358,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_359,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_18,c_16,c_58])).

cnf(c_364,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_393,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_yellow_0(sK1,sK2) != X0
    | k1_yellow_0(sK1,sK3) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_364])).

cnf(c_394,plain,
    ( ~ r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
    | ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_584,plain,
    ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_567,c_394])).

cnf(c_588,plain,
    ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_571,c_584])).

cnf(c_818,plain,
    ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_588])).

cnf(c_1027,plain,
    ( r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1026,plain,
    ( m1_subset_1(k1_yellow_0(sK1,X0_51),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_1036,plain,
    ( r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1027,c_1026])).

cnf(c_1077,plain,
    ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1036])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1174,c_1099,c_1098,c_1095,c_1077])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.98/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.98/0.98  
% 0.98/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.98/0.98  
% 0.98/0.98  ------  iProver source info
% 0.98/0.98  
% 0.98/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.98/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.98/0.98  git: non_committed_changes: false
% 0.98/0.98  git: last_make_outside_of_git: false
% 0.98/0.98  
% 0.98/0.98  ------ 
% 0.98/0.98  
% 0.98/0.98  ------ Input Options
% 0.98/0.98  
% 0.98/0.98  --out_options                           all
% 0.98/0.98  --tptp_safe_out                         true
% 0.98/0.98  --problem_path                          ""
% 0.98/0.98  --include_path                          ""
% 0.98/0.98  --clausifier                            res/vclausify_rel
% 0.98/0.98  --clausifier_options                    --mode clausify
% 0.98/0.98  --stdin                                 false
% 0.98/0.98  --stats_out                             all
% 0.98/0.98  
% 0.98/0.98  ------ General Options
% 0.98/0.98  
% 0.98/0.98  --fof                                   false
% 0.98/0.98  --time_out_real                         305.
% 0.98/0.98  --time_out_virtual                      -1.
% 0.98/0.98  --symbol_type_check                     false
% 0.98/0.98  --clausify_out                          false
% 0.98/0.98  --sig_cnt_out                           false
% 0.98/0.98  --trig_cnt_out                          false
% 0.98/0.98  --trig_cnt_out_tolerance                1.
% 0.98/0.98  --trig_cnt_out_sk_spl                   false
% 0.98/0.98  --abstr_cl_out                          false
% 0.98/0.98  
% 0.98/0.98  ------ Global Options
% 0.98/0.98  
% 0.98/0.98  --schedule                              default
% 0.98/0.98  --add_important_lit                     false
% 0.98/0.98  --prop_solver_per_cl                    1000
% 0.98/0.98  --min_unsat_core                        false
% 0.98/0.98  --soft_assumptions                      false
% 0.98/0.98  --soft_lemma_size                       3
% 0.98/0.98  --prop_impl_unit_size                   0
% 0.98/0.98  --prop_impl_unit                        []
% 0.98/0.98  --share_sel_clauses                     true
% 0.98/0.98  --reset_solvers                         false
% 0.98/0.98  --bc_imp_inh                            [conj_cone]
% 0.98/0.98  --conj_cone_tolerance                   3.
% 0.98/0.98  --extra_neg_conj                        none
% 0.98/0.98  --large_theory_mode                     true
% 0.98/0.98  --prolific_symb_bound                   200
% 0.98/0.98  --lt_threshold                          2000
% 0.98/0.98  --clause_weak_htbl                      true
% 0.98/0.98  --gc_record_bc_elim                     false
% 0.98/0.98  
% 0.98/0.98  ------ Preprocessing Options
% 0.98/0.98  
% 0.98/0.98  --preprocessing_flag                    true
% 0.98/0.98  --time_out_prep_mult                    0.1
% 0.98/0.98  --splitting_mode                        input
% 0.98/0.98  --splitting_grd                         true
% 0.98/0.98  --splitting_cvd                         false
% 0.98/0.98  --splitting_cvd_svl                     false
% 0.98/0.98  --splitting_nvd                         32
% 0.98/0.98  --sub_typing                            true
% 0.98/0.98  --prep_gs_sim                           true
% 0.98/0.98  --prep_unflatten                        true
% 0.98/0.98  --prep_res_sim                          true
% 0.98/0.98  --prep_upred                            true
% 0.98/0.98  --prep_sem_filter                       exhaustive
% 0.98/0.98  --prep_sem_filter_out                   false
% 0.98/0.98  --pred_elim                             true
% 0.98/0.98  --res_sim_input                         true
% 0.98/0.98  --eq_ax_congr_red                       true
% 0.98/0.98  --pure_diseq_elim                       true
% 0.98/0.98  --brand_transform                       false
% 0.98/0.98  --non_eq_to_eq                          false
% 0.98/0.98  --prep_def_merge                        true
% 0.98/0.98  --prep_def_merge_prop_impl              false
% 0.98/0.98  --prep_def_merge_mbd                    true
% 0.98/0.98  --prep_def_merge_tr_red                 false
% 0.98/0.98  --prep_def_merge_tr_cl                  false
% 0.98/0.98  --smt_preprocessing                     true
% 0.98/0.98  --smt_ac_axioms                         fast
% 0.98/0.98  --preprocessed_out                      false
% 0.98/0.98  --preprocessed_stats                    false
% 0.98/0.98  
% 0.98/0.98  ------ Abstraction refinement Options
% 0.98/0.98  
% 0.98/0.98  --abstr_ref                             []
% 0.98/0.98  --abstr_ref_prep                        false
% 0.98/0.98  --abstr_ref_until_sat                   false
% 0.98/0.98  --abstr_ref_sig_restrict                funpre
% 0.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/0.98  --abstr_ref_under                       []
% 0.98/0.98  
% 0.98/0.98  ------ SAT Options
% 0.98/0.98  
% 0.98/0.98  --sat_mode                              false
% 0.98/0.98  --sat_fm_restart_options                ""
% 0.98/0.98  --sat_gr_def                            false
% 0.98/0.98  --sat_epr_types                         true
% 0.98/0.98  --sat_non_cyclic_types                  false
% 0.98/0.98  --sat_finite_models                     false
% 0.98/0.98  --sat_fm_lemmas                         false
% 0.98/0.98  --sat_fm_prep                           false
% 0.98/0.98  --sat_fm_uc_incr                        true
% 0.98/0.98  --sat_out_model                         small
% 0.98/0.98  --sat_out_clauses                       false
% 0.98/0.98  
% 0.98/0.98  ------ QBF Options
% 0.98/0.98  
% 0.98/0.98  --qbf_mode                              false
% 0.98/0.98  --qbf_elim_univ                         false
% 0.98/0.98  --qbf_dom_inst                          none
% 0.98/0.98  --qbf_dom_pre_inst                      false
% 0.98/0.98  --qbf_sk_in                             false
% 0.98/0.98  --qbf_pred_elim                         true
% 0.98/0.98  --qbf_split                             512
% 0.98/0.98  
% 0.98/0.98  ------ BMC1 Options
% 0.98/0.98  
% 0.98/0.98  --bmc1_incremental                      false
% 0.98/0.98  --bmc1_axioms                           reachable_all
% 0.98/0.98  --bmc1_min_bound                        0
% 0.98/0.98  --bmc1_max_bound                        -1
% 0.98/0.98  --bmc1_max_bound_default                -1
% 0.98/0.98  --bmc1_symbol_reachability              true
% 0.98/0.98  --bmc1_property_lemmas                  false
% 0.98/0.98  --bmc1_k_induction                      false
% 0.98/0.98  --bmc1_non_equiv_states                 false
% 0.98/0.98  --bmc1_deadlock                         false
% 0.98/0.98  --bmc1_ucm                              false
% 0.98/0.98  --bmc1_add_unsat_core                   none
% 0.98/0.98  --bmc1_unsat_core_children              false
% 0.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/0.98  --bmc1_out_stat                         full
% 0.98/0.98  --bmc1_ground_init                      false
% 0.98/0.98  --bmc1_pre_inst_next_state              false
% 0.98/0.98  --bmc1_pre_inst_state                   false
% 0.98/0.98  --bmc1_pre_inst_reach_state             false
% 0.98/0.98  --bmc1_out_unsat_core                   false
% 0.98/0.98  --bmc1_aig_witness_out                  false
% 0.98/0.98  --bmc1_verbose                          false
% 0.98/0.98  --bmc1_dump_clauses_tptp                false
% 0.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.98/0.98  --bmc1_dump_file                        -
% 0.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.98/0.98  --bmc1_ucm_extend_mode                  1
% 0.98/0.98  --bmc1_ucm_init_mode                    2
% 0.98/0.98  --bmc1_ucm_cone_mode                    none
% 0.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.98/0.98  --bmc1_ucm_relax_model                  4
% 0.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/0.98  --bmc1_ucm_layered_model                none
% 0.98/0.98  --bmc1_ucm_max_lemma_size               10
% 0.98/0.98  
% 0.98/0.98  ------ AIG Options
% 0.98/0.98  
% 0.98/0.98  --aig_mode                              false
% 0.98/0.98  
% 0.98/0.98  ------ Instantiation Options
% 0.98/0.98  
% 0.98/0.98  --instantiation_flag                    true
% 0.98/0.98  --inst_sos_flag                         false
% 0.98/0.98  --inst_sos_phase                        true
% 0.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/0.98  --inst_lit_sel_side                     num_symb
% 0.98/0.98  --inst_solver_per_active                1400
% 0.98/0.98  --inst_solver_calls_frac                1.
% 0.98/0.98  --inst_passive_queue_type               priority_queues
% 0.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/0.98  --inst_passive_queues_freq              [25;2]
% 0.98/0.98  --inst_dismatching                      true
% 0.98/0.98  --inst_eager_unprocessed_to_passive     true
% 0.98/0.98  --inst_prop_sim_given                   true
% 0.98/0.98  --inst_prop_sim_new                     false
% 0.98/0.98  --inst_subs_new                         false
% 0.98/0.98  --inst_eq_res_simp                      false
% 0.98/0.98  --inst_subs_given                       false
% 0.98/0.98  --inst_orphan_elimination               true
% 0.98/0.98  --inst_learning_loop_flag               true
% 0.98/0.98  --inst_learning_start                   3000
% 0.98/0.98  --inst_learning_factor                  2
% 0.98/0.98  --inst_start_prop_sim_after_learn       3
% 0.98/0.98  --inst_sel_renew                        solver
% 0.98/0.98  --inst_lit_activity_flag                true
% 0.98/0.98  --inst_restr_to_given                   false
% 0.98/0.98  --inst_activity_threshold               500
% 0.98/0.98  --inst_out_proof                        true
% 0.98/0.98  
% 0.98/0.98  ------ Resolution Options
% 0.98/0.98  
% 0.98/0.98  --resolution_flag                       true
% 0.98/0.98  --res_lit_sel                           adaptive
% 0.98/0.98  --res_lit_sel_side                      none
% 0.98/0.98  --res_ordering                          kbo
% 0.98/0.98  --res_to_prop_solver                    active
% 0.98/0.98  --res_prop_simpl_new                    false
% 0.98/0.98  --res_prop_simpl_given                  true
% 0.98/0.98  --res_passive_queue_type                priority_queues
% 0.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/0.98  --res_passive_queues_freq               [15;5]
% 0.98/0.98  --res_forward_subs                      full
% 0.98/0.98  --res_backward_subs                     full
% 0.98/0.98  --res_forward_subs_resolution           true
% 0.98/0.98  --res_backward_subs_resolution          true
% 0.98/0.98  --res_orphan_elimination                true
% 0.98/0.98  --res_time_limit                        2.
% 0.98/0.98  --res_out_proof                         true
% 0.98/0.98  
% 0.98/0.98  ------ Superposition Options
% 0.98/0.98  
% 0.98/0.98  --superposition_flag                    true
% 0.98/0.98  --sup_passive_queue_type                priority_queues
% 0.98/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.98/0.98  --demod_completeness_check              fast
% 0.98/0.98  --demod_use_ground                      true
% 0.98/0.98  --sup_to_prop_solver                    passive
% 0.98/0.98  --sup_prop_simpl_new                    true
% 0.98/0.98  --sup_prop_simpl_given                  true
% 0.98/0.98  --sup_fun_splitting                     false
% 0.98/0.98  --sup_smt_interval                      50000
% 0.98/0.98  
% 0.98/0.98  ------ Superposition Simplification Setup
% 0.98/0.98  
% 0.98/0.98  --sup_indices_passive                   []
% 0.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.98  --sup_full_bw                           [BwDemod]
% 0.98/0.98  --sup_immed_triv                        [TrivRules]
% 0.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.98  --sup_immed_bw_main                     []
% 0.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.98  
% 0.98/0.98  ------ Combination Options
% 0.98/0.98  
% 0.98/0.98  --comb_res_mult                         3
% 0.98/0.98  --comb_sup_mult                         2
% 0.98/0.98  --comb_inst_mult                        10
% 0.98/0.98  
% 0.98/0.98  ------ Debug Options
% 0.98/0.98  
% 0.98/0.98  --dbg_backtrace                         false
% 0.98/0.98  --dbg_dump_prop_clauses                 false
% 0.98/0.98  --dbg_dump_prop_clauses_file            -
% 0.98/0.98  --dbg_out_stat                          false
% 0.98/0.98  ------ Parsing...
% 0.98/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.98/0.98  
% 0.98/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 0.98/0.98  
% 0.98/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.98/0.98  
% 0.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.98/0.98  ------ Proving...
% 0.98/0.98  ------ Problem Properties 
% 0.98/0.98  
% 0.98/0.98  
% 0.98/0.98  clauses                                 9
% 0.98/0.98  conjectures                             0
% 0.98/0.98  EPR                                     0
% 0.98/0.98  Horn                                    7
% 0.98/0.98  unary                                   3
% 0.98/0.98  binary                                  1
% 0.98/0.98  lits                                    23
% 0.98/0.98  lits eq                                 3
% 0.98/0.98  fd_pure                                 0
% 0.98/0.98  fd_pseudo                               0
% 0.98/0.98  fd_cond                                 0
% 0.98/0.98  fd_pseudo_cond                          3
% 0.98/0.98  AC symbols                              0
% 0.98/0.98  
% 0.98/0.98  ------ Schedule dynamic 5 is on 
% 0.98/0.98  
% 0.98/0.98  ------ no conjectures: strip conj schedule 
% 0.98/0.98  
% 0.98/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.98/0.98  
% 0.98/0.98  
% 0.98/0.98  ------ 
% 0.98/0.98  Current options:
% 0.98/0.98  ------ 
% 0.98/0.98  
% 0.98/0.98  ------ Input Options
% 0.98/0.98  
% 0.98/0.98  --out_options                           all
% 0.98/0.98  --tptp_safe_out                         true
% 0.98/0.98  --problem_path                          ""
% 0.98/0.98  --include_path                          ""
% 0.98/0.98  --clausifier                            res/vclausify_rel
% 0.98/0.98  --clausifier_options                    --mode clausify
% 0.98/0.98  --stdin                                 false
% 0.98/0.98  --stats_out                             all
% 0.98/0.98  
% 0.98/0.98  ------ General Options
% 0.98/0.98  
% 0.98/0.98  --fof                                   false
% 0.98/0.98  --time_out_real                         305.
% 0.98/0.98  --time_out_virtual                      -1.
% 0.98/0.98  --symbol_type_check                     false
% 0.98/0.98  --clausify_out                          false
% 0.98/0.98  --sig_cnt_out                           false
% 0.98/0.98  --trig_cnt_out                          false
% 0.98/0.98  --trig_cnt_out_tolerance                1.
% 0.98/0.98  --trig_cnt_out_sk_spl                   false
% 0.98/0.98  --abstr_cl_out                          false
% 0.98/0.98  
% 0.98/0.98  ------ Global Options
% 0.98/0.98  
% 0.98/0.98  --schedule                              default
% 0.98/0.98  --add_important_lit                     false
% 0.98/0.98  --prop_solver_per_cl                    1000
% 0.98/0.98  --min_unsat_core                        false
% 0.98/0.98  --soft_assumptions                      false
% 0.98/0.98  --soft_lemma_size                       3
% 0.98/0.98  --prop_impl_unit_size                   0
% 0.98/0.98  --prop_impl_unit                        []
% 0.98/0.98  --share_sel_clauses                     true
% 0.98/0.98  --reset_solvers                         false
% 0.98/0.98  --bc_imp_inh                            [conj_cone]
% 0.98/0.98  --conj_cone_tolerance                   3.
% 0.98/0.98  --extra_neg_conj                        none
% 0.98/0.98  --large_theory_mode                     true
% 0.98/0.98  --prolific_symb_bound                   200
% 0.98/0.98  --lt_threshold                          2000
% 0.98/0.98  --clause_weak_htbl                      true
% 0.98/0.98  --gc_record_bc_elim                     false
% 0.98/0.98  
% 0.98/0.98  ------ Preprocessing Options
% 0.98/0.98  
% 0.98/0.98  --preprocessing_flag                    true
% 0.98/0.98  --time_out_prep_mult                    0.1
% 0.98/0.98  --splitting_mode                        input
% 0.98/0.98  --splitting_grd                         true
% 0.98/0.98  --splitting_cvd                         false
% 0.98/0.98  --splitting_cvd_svl                     false
% 0.98/0.98  --splitting_nvd                         32
% 0.98/0.98  --sub_typing                            true
% 0.98/0.98  --prep_gs_sim                           true
% 0.98/0.98  --prep_unflatten                        true
% 0.98/0.98  --prep_res_sim                          true
% 0.98/0.98  --prep_upred                            true
% 0.98/0.98  --prep_sem_filter                       exhaustive
% 0.98/0.98  --prep_sem_filter_out                   false
% 0.98/0.98  --pred_elim                             true
% 0.98/0.98  --res_sim_input                         true
% 0.98/0.98  --eq_ax_congr_red                       true
% 0.98/0.98  --pure_diseq_elim                       true
% 0.98/0.98  --brand_transform                       false
% 0.98/0.98  --non_eq_to_eq                          false
% 0.98/0.98  --prep_def_merge                        true
% 0.98/0.98  --prep_def_merge_prop_impl              false
% 0.98/0.98  --prep_def_merge_mbd                    true
% 0.98/0.98  --prep_def_merge_tr_red                 false
% 0.98/0.98  --prep_def_merge_tr_cl                  false
% 0.98/0.98  --smt_preprocessing                     true
% 0.98/0.98  --smt_ac_axioms                         fast
% 0.98/0.98  --preprocessed_out                      false
% 0.98/0.98  --preprocessed_stats                    false
% 0.98/0.98  
% 0.98/0.98  ------ Abstraction refinement Options
% 0.98/0.98  
% 0.98/0.98  --abstr_ref                             []
% 0.98/0.98  --abstr_ref_prep                        false
% 0.98/0.98  --abstr_ref_until_sat                   false
% 0.98/0.98  --abstr_ref_sig_restrict                funpre
% 0.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/0.98  --abstr_ref_under                       []
% 0.98/0.98  
% 0.98/0.98  ------ SAT Options
% 0.98/0.98  
% 0.98/0.98  --sat_mode                              false
% 0.98/0.98  --sat_fm_restart_options                ""
% 0.98/0.98  --sat_gr_def                            false
% 0.98/0.98  --sat_epr_types                         true
% 0.98/0.98  --sat_non_cyclic_types                  false
% 0.98/0.98  --sat_finite_models                     false
% 0.98/0.98  --sat_fm_lemmas                         false
% 0.98/0.98  --sat_fm_prep                           false
% 0.98/0.98  --sat_fm_uc_incr                        true
% 0.98/0.98  --sat_out_model                         small
% 0.98/0.98  --sat_out_clauses                       false
% 0.98/0.98  
% 0.98/0.98  ------ QBF Options
% 0.98/0.98  
% 0.98/0.98  --qbf_mode                              false
% 0.98/0.98  --qbf_elim_univ                         false
% 0.98/0.98  --qbf_dom_inst                          none
% 0.98/0.98  --qbf_dom_pre_inst                      false
% 0.98/0.98  --qbf_sk_in                             false
% 0.98/0.98  --qbf_pred_elim                         true
% 0.98/0.98  --qbf_split                             512
% 0.98/0.98  
% 0.98/0.98  ------ BMC1 Options
% 0.98/0.98  
% 0.98/0.98  --bmc1_incremental                      false
% 0.98/0.98  --bmc1_axioms                           reachable_all
% 0.98/0.98  --bmc1_min_bound                        0
% 0.98/0.98  --bmc1_max_bound                        -1
% 0.98/0.98  --bmc1_max_bound_default                -1
% 0.98/0.98  --bmc1_symbol_reachability              true
% 0.98/0.98  --bmc1_property_lemmas                  false
% 0.98/0.98  --bmc1_k_induction                      false
% 0.98/0.98  --bmc1_non_equiv_states                 false
% 0.98/0.98  --bmc1_deadlock                         false
% 0.98/0.98  --bmc1_ucm                              false
% 0.98/0.98  --bmc1_add_unsat_core                   none
% 0.98/0.98  --bmc1_unsat_core_children              false
% 0.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/0.98  --bmc1_out_stat                         full
% 0.98/0.98  --bmc1_ground_init                      false
% 0.98/0.98  --bmc1_pre_inst_next_state              false
% 0.98/0.98  --bmc1_pre_inst_state                   false
% 0.98/0.98  --bmc1_pre_inst_reach_state             false
% 0.98/0.98  --bmc1_out_unsat_core                   false
% 0.98/0.98  --bmc1_aig_witness_out                  false
% 0.98/0.98  --bmc1_verbose                          false
% 0.98/0.98  --bmc1_dump_clauses_tptp                false
% 0.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.98/0.98  --bmc1_dump_file                        -
% 0.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.98/0.98  --bmc1_ucm_extend_mode                  1
% 0.98/0.98  --bmc1_ucm_init_mode                    2
% 0.98/0.98  --bmc1_ucm_cone_mode                    none
% 0.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.98/0.98  --bmc1_ucm_relax_model                  4
% 0.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/0.98  --bmc1_ucm_layered_model                none
% 0.98/0.98  --bmc1_ucm_max_lemma_size               10
% 0.98/0.98  
% 0.98/0.98  ------ AIG Options
% 0.98/0.98  
% 0.98/0.98  --aig_mode                              false
% 0.98/0.98  
% 0.98/0.98  ------ Instantiation Options
% 0.98/0.98  
% 0.98/0.98  --instantiation_flag                    true
% 0.98/0.98  --inst_sos_flag                         false
% 0.98/0.98  --inst_sos_phase                        true
% 0.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/0.98  --inst_lit_sel_side                     none
% 0.98/0.98  --inst_solver_per_active                1400
% 0.98/0.98  --inst_solver_calls_frac                1.
% 0.98/0.98  --inst_passive_queue_type               priority_queues
% 0.98/0.98  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.98/0.98  --inst_passive_queues_freq              [25;2]
% 0.98/0.98  --inst_dismatching                      true
% 0.98/0.98  --inst_eager_unprocessed_to_passive     true
% 0.98/0.98  --inst_prop_sim_given                   true
% 0.98/0.98  --inst_prop_sim_new                     false
% 0.98/0.98  --inst_subs_new                         false
% 0.98/0.98  --inst_eq_res_simp                      false
% 0.98/0.98  --inst_subs_given                       false
% 0.98/0.98  --inst_orphan_elimination               true
% 0.98/0.98  --inst_learning_loop_flag               true
% 0.98/0.98  --inst_learning_start                   3000
% 0.98/0.98  --inst_learning_factor                  2
% 0.98/0.98  --inst_start_prop_sim_after_learn       3
% 0.98/0.98  --inst_sel_renew                        solver
% 0.98/0.98  --inst_lit_activity_flag                true
% 0.98/0.98  --inst_restr_to_given                   false
% 0.98/0.98  --inst_activity_threshold               500
% 0.98/0.98  --inst_out_proof                        true
% 0.98/0.98  
% 0.98/0.98  ------ Resolution Options
% 0.98/0.98  
% 0.98/0.98  --resolution_flag                       false
% 0.98/0.98  --res_lit_sel                           adaptive
% 0.98/0.98  --res_lit_sel_side                      none
% 0.98/0.98  --res_ordering                          kbo
% 0.98/0.98  --res_to_prop_solver                    active
% 0.98/0.98  --res_prop_simpl_new                    false
% 0.98/0.98  --res_prop_simpl_given                  true
% 0.98/0.98  --res_passive_queue_type                priority_queues
% 0.98/0.98  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.98/0.98  --res_passive_queues_freq               [15;5]
% 0.98/0.98  --res_forward_subs                      full
% 0.98/0.98  --res_backward_subs                     full
% 0.98/0.98  --res_forward_subs_resolution           true
% 0.98/0.98  --res_backward_subs_resolution          true
% 0.98/0.98  --res_orphan_elimination                true
% 0.98/0.98  --res_time_limit                        2.
% 0.98/0.98  --res_out_proof                         true
% 0.98/0.98  
% 0.98/0.98  ------ Superposition Options
% 0.98/0.98  
% 0.98/0.98  --superposition_flag                    true
% 0.98/0.98  --sup_passive_queue_type                priority_queues
% 0.98/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.98/0.99  --demod_completeness_check              fast
% 0.98/0.99  --demod_use_ground                      true
% 0.98/0.99  --sup_to_prop_solver                    passive
% 0.98/0.99  --sup_prop_simpl_new                    true
% 0.98/0.99  --sup_prop_simpl_given                  true
% 0.98/0.99  --sup_fun_splitting                     false
% 0.98/0.99  --sup_smt_interval                      50000
% 0.98/0.99  
% 0.98/0.99  ------ Superposition Simplification Setup
% 0.98/0.99  
% 0.98/0.99  --sup_indices_passive                   []
% 0.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_full_bw                           [BwDemod]
% 0.98/0.99  --sup_immed_triv                        [TrivRules]
% 0.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_immed_bw_main                     []
% 0.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.99  
% 0.98/0.99  ------ Combination Options
% 0.98/0.99  
% 0.98/0.99  --comb_res_mult                         3
% 0.98/0.99  --comb_sup_mult                         2
% 0.98/0.99  --comb_inst_mult                        10
% 0.98/0.99  
% 0.98/0.99  ------ Debug Options
% 0.98/0.99  
% 0.98/0.99  --dbg_backtrace                         false
% 0.98/0.99  --dbg_dump_prop_clauses                 false
% 0.98/0.99  --dbg_dump_prop_clauses_file            -
% 0.98/0.99  --dbg_out_stat                          false
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  ------ Proving...
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  % SZS status Theorem for theBenchmark.p
% 0.98/0.99  
% 0.98/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.98/0.99  
% 0.98/0.99  fof(f3,axiom,(
% 0.98/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f16,plain,(
% 0.98/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(ennf_transformation,[],[f3])).
% 0.98/0.99  
% 0.98/0.99  fof(f17,plain,(
% 0.98/0.99    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(flattening,[],[f16])).
% 0.98/0.99  
% 0.98/0.99  fof(f27,plain,(
% 0.98/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(nnf_transformation,[],[f17])).
% 0.98/0.99  
% 0.98/0.99  fof(f28,plain,(
% 0.98/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(flattening,[],[f27])).
% 0.98/0.99  
% 0.98/0.99  fof(f29,plain,(
% 0.98/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(rectify,[],[f28])).
% 0.98/0.99  
% 0.98/0.99  fof(f30,plain,(
% 0.98/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 0.98/0.99    introduced(choice_axiom,[])).
% 0.98/0.99  
% 0.98/0.99  fof(f31,plain,(
% 0.98/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 0.98/0.99  
% 0.98/0.99  fof(f39,plain,(
% 0.98/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f31])).
% 0.98/0.99  
% 0.98/0.99  fof(f56,plain,(
% 0.98/0.99    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.98/0.99    inference(equality_resolution,[],[f39])).
% 0.98/0.99  
% 0.98/0.99  fof(f4,axiom,(
% 0.98/0.99    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f18,plain,(
% 0.98/0.99    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(ennf_transformation,[],[f4])).
% 0.98/0.99  
% 0.98/0.99  fof(f43,plain,(
% 0.98/0.99    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f18])).
% 0.98/0.99  
% 0.98/0.99  fof(f5,axiom,(
% 0.98/0.99    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)))),
% 0.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f19,plain,(
% 0.98/0.99    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.98/0.99    inference(ennf_transformation,[],[f5])).
% 0.98/0.99  
% 0.98/0.99  fof(f20,plain,(
% 0.98/0.99    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.98/0.99    inference(flattening,[],[f19])).
% 0.98/0.99  
% 0.98/0.99  fof(f44,plain,(
% 0.98/0.99    ( ! [X0,X1] : (r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f20])).
% 0.98/0.99  
% 0.98/0.99  fof(f8,conjecture,(
% 0.98/0.99    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f9,negated_conjecture,(
% 0.98/0.99    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.98/0.99    inference(negated_conjecture,[],[f8])).
% 0.98/0.99  
% 0.98/0.99  fof(f10,plain,(
% 0.98/0.99    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.98/0.99    inference(pure_predicate_removal,[],[f9])).
% 0.98/0.99  
% 0.98/0.99  fof(f11,plain,(
% 0.98/0.99    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.08/0.99    inference(pure_predicate_removal,[],[f10])).
% 1.08/0.99  
% 1.08/0.99  fof(f24,plain,(
% 1.08/0.99    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & (l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.08/0.99    inference(ennf_transformation,[],[f11])).
% 1.08/0.99  
% 1.08/0.99  fof(f25,plain,(
% 1.08/0.99    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.08/0.99    inference(flattening,[],[f24])).
% 1.08/0.99  
% 1.08/0.99  fof(f33,plain,(
% 1.08/0.99    ( ! [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) => ((~r1_orders_2(X0,k2_yellow_0(X0,sK3),k2_yellow_0(X0,sK2)) | ~r3_orders_2(X0,k1_yellow_0(X0,sK2),k1_yellow_0(X0,sK3))) & r1_tarski(sK2,sK3))) )),
% 1.08/0.99    introduced(choice_axiom,[])).
% 1.08/0.99  
% 1.08/0.99  fof(f32,plain,(
% 1.08/0.99    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X2,X1] : ((~r1_orders_2(sK1,k2_yellow_0(sK1,X2),k2_yellow_0(sK1,X1)) | ~r3_orders_2(sK1,k1_yellow_0(sK1,X1),k1_yellow_0(sK1,X2))) & r1_tarski(X1,X2)) & l1_orders_2(sK1) & v3_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1))),
% 1.08/0.99    introduced(choice_axiom,[])).
% 1.08/0.99  
% 1.08/0.99  fof(f34,plain,(
% 1.08/0.99    ((~r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2)) | ~r3_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))) & r1_tarski(sK2,sK3)) & l1_orders_2(sK1) & v3_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1)),
% 1.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f33,f32])).
% 1.08/0.99  
% 1.08/0.99  fof(f52,plain,(
% 1.08/0.99    v3_lattice3(sK1)),
% 1.08/0.99    inference(cnf_transformation,[],[f34])).
% 1.08/0.99  
% 1.08/0.99  fof(f50,plain,(
% 1.08/0.99    v5_orders_2(sK1)),
% 1.08/0.99    inference(cnf_transformation,[],[f34])).
% 1.08/0.99  
% 1.08/0.99  fof(f51,plain,(
% 1.08/0.99    v1_lattice3(sK1)),
% 1.08/0.99    inference(cnf_transformation,[],[f34])).
% 1.08/0.99  
% 1.08/0.99  fof(f53,plain,(
% 1.08/0.99    l1_orders_2(sK1)),
% 1.08/0.99    inference(cnf_transformation,[],[f34])).
% 1.08/0.99  
% 1.08/0.99  fof(f2,axiom,(
% 1.08/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.99  
% 1.08/0.99  fof(f14,plain,(
% 1.08/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.08/0.99    inference(ennf_transformation,[],[f2])).
% 1.08/0.99  
% 1.08/0.99  fof(f15,plain,(
% 1.08/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.08/0.99    inference(flattening,[],[f14])).
% 1.08/0.99  
% 1.08/0.99  fof(f37,plain,(
% 1.08/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.08/0.99    inference(cnf_transformation,[],[f15])).
% 1.08/0.99  
% 1.08/0.99  fof(f38,plain,(
% 1.08/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.08/0.99    inference(cnf_transformation,[],[f31])).
% 1.08/0.99  
% 1.08/0.99  fof(f57,plain,(
% 1.08/0.99    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.08/0.99    inference(equality_resolution,[],[f38])).
% 1.08/0.99  
% 1.08/0.99  fof(f7,axiom,(
% 1.08/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 1.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.99  
% 1.08/0.99  fof(f23,plain,(
% 1.08/0.99    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.08/0.99    inference(ennf_transformation,[],[f7])).
% 1.08/0.99  
% 1.08/0.99  fof(f48,plain,(
% 1.08/0.99    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 1.08/0.99    inference(cnf_transformation,[],[f23])).
% 1.08/0.99  
% 1.08/0.99  fof(f54,plain,(
% 1.08/0.99    r1_tarski(sK2,sK3)),
% 1.08/0.99    inference(cnf_transformation,[],[f34])).
% 1.08/0.99  
% 1.08/0.99  fof(f6,axiom,(
% 1.08/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r2_yellow_0(X0,X2) & r2_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))))),
% 1.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.99  
% 1.08/0.99  fof(f21,plain,(
% 1.08/0.99    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | (~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 1.08/0.99    inference(ennf_transformation,[],[f6])).
% 1.08/0.99  
% 1.08/0.99  fof(f22,plain,(
% 1.08/0.99    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.08/0.99    inference(flattening,[],[f21])).
% 1.08/0.99  
% 1.08/0.99  fof(f46,plain,(
% 1.08/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 1.08/0.99    inference(cnf_transformation,[],[f22])).
% 1.08/0.99  
% 1.08/0.99  fof(f45,plain,(
% 1.08/0.99    ( ! [X0,X1] : (r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.08/0.99    inference(cnf_transformation,[],[f20])).
% 1.08/0.99  
% 1.08/0.99  fof(f55,plain,(
% 1.08/0.99    ~r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2)) | ~r3_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))),
% 1.08/0.99    inference(cnf_transformation,[],[f34])).
% 1.08/0.99  
% 1.08/0.99  fof(f1,axiom,(
% 1.08/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.99  
% 1.08/0.99  fof(f12,plain,(
% 1.08/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.08/0.99    inference(ennf_transformation,[],[f1])).
% 1.08/0.99  
% 1.08/0.99  fof(f13,plain,(
% 1.08/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.08/0.99    inference(flattening,[],[f12])).
% 1.08/0.99  
% 1.08/0.99  fof(f26,plain,(
% 1.08/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.08/0.99    inference(nnf_transformation,[],[f13])).
% 1.08/0.99  
% 1.08/0.99  fof(f36,plain,(
% 1.08/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.08/0.99    inference(cnf_transformation,[],[f26])).
% 1.08/0.99  
% 1.08/0.99  fof(f49,plain,(
% 1.08/0.99    v3_orders_2(sK1)),
% 1.08/0.99    inference(cnf_transformation,[],[f34])).
% 1.08/0.99  
% 1.08/0.99  cnf(c_6,plain,
% 1.08/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.08/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.08/0.99      | ~ r1_yellow_0(X0,X1)
% 1.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_8,plain,
% 1.08/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_129,plain,
% 1.08/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.99      | ~ r1_yellow_0(X0,X1)
% 1.08/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.08/0.99      | ~ r2_lattice3(X0,X1,X2)
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6,c_8]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_130,plain,
% 1.08/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.08/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.08/0.99      | ~ r1_yellow_0(X0,X1)
% 1.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(renaming,[status(thm)],[c_129]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_10,plain,
% 1.08/0.99      ( r1_yellow_0(X0,X1)
% 1.08/0.99      | ~ v5_orders_2(X0)
% 1.08/0.99      | ~ v3_lattice3(X0)
% 1.08/0.99      | v2_struct_0(X0)
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_17,negated_conjecture,
% 1.08/0.99      ( v3_lattice3(sK1) ),
% 1.08/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_254,plain,
% 1.08/0.99      ( r1_yellow_0(X0,X1)
% 1.08/0.99      | ~ v5_orders_2(X0)
% 1.08/0.99      | v2_struct_0(X0)
% 1.08/0.99      | ~ l1_orders_2(X0)
% 1.08/0.99      | sK1 != X0 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_255,plain,
% 1.08/0.99      ( r1_yellow_0(sK1,X0)
% 1.08/0.99      | ~ v5_orders_2(sK1)
% 1.08/0.99      | v2_struct_0(sK1)
% 1.08/0.99      | ~ l1_orders_2(sK1) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_254]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_19,negated_conjecture,
% 1.08/0.99      ( v5_orders_2(sK1) ),
% 1.08/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_18,negated_conjecture,
% 1.08/0.99      ( v1_lattice3(sK1) ),
% 1.08/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_16,negated_conjecture,
% 1.08/0.99      ( l1_orders_2(sK1) ),
% 1.08/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_2,plain,
% 1.08/0.99      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_58,plain,
% 1.08/0.99      ( ~ v1_lattice3(sK1) | ~ v2_struct_0(sK1) | ~ l1_orders_2(sK1) ),
% 1.08/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_259,plain,
% 1.08/0.99      ( r1_yellow_0(sK1,X0) ),
% 1.08/0.99      inference(global_propositional_subsumption,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_255,c_19,c_18,c_16,c_58]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_414,plain,
% 1.08/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.08/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.99      | ~ l1_orders_2(X0)
% 1.08/0.99      | X3 != X1
% 1.08/0.99      | sK1 != X0 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_130,c_259]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_415,plain,
% 1.08/0.99      ( ~ r2_lattice3(sK1,X0,X1)
% 1.08/0.99      | r1_orders_2(sK1,k1_yellow_0(sK1,X0),X1)
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.08/0.99      | ~ l1_orders_2(sK1) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_419,plain,
% 1.08/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.08/0.99      | r1_orders_2(sK1,k1_yellow_0(sK1,X0),X1)
% 1.08/0.99      | ~ r2_lattice3(sK1,X0,X1) ),
% 1.08/0.99      inference(global_propositional_subsumption,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_415,c_16]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_420,plain,
% 1.08/0.99      ( ~ r2_lattice3(sK1,X0,X1)
% 1.08/0.99      | r1_orders_2(sK1,k1_yellow_0(sK1,X0),X1)
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.08/0.99      inference(renaming,[status(thm)],[c_419]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_826,plain,
% 1.08/0.99      ( ~ r2_lattice3(sK1,X0_51,X0_50)
% 1.08/0.99      | r1_orders_2(sK1,k1_yellow_0(sK1,X0_51),X0_50)
% 1.08/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK1)) ),
% 1.08/0.99      inference(subtyping,[status(esa)],[c_420]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1104,plain,
% 1.08/0.99      ( ~ r2_lattice3(sK1,X0_51,k1_yellow_0(sK1,X1_51))
% 1.08/0.99      | r1_orders_2(sK1,k1_yellow_0(sK1,X0_51),k1_yellow_0(sK1,X1_51))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,X1_51),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(instantiation,[status(thm)],[c_826]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1174,plain,
% 1.08/0.99      ( ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
% 1.08/0.99      | r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(instantiation,[status(thm)],[c_1104]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_7,plain,
% 1.08/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.08/0.99      | ~ r1_yellow_0(X0,X1)
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_122,plain,
% 1.08/0.99      ( ~ r1_yellow_0(X0,X1)
% 1.08/0.99      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_7,c_8]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_123,plain,
% 1.08/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.08/0.99      | ~ r1_yellow_0(X0,X1)
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(renaming,[status(thm)],[c_122]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_435,plain,
% 1.08/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.08/0.99      | ~ l1_orders_2(X0)
% 1.08/0.99      | X2 != X1
% 1.08/0.99      | sK1 != X0 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_123,c_259]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_436,plain,
% 1.08/0.99      ( r2_lattice3(sK1,X0,k1_yellow_0(sK1,X0)) | ~ l1_orders_2(sK1) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_435]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_440,plain,
% 1.08/0.99      ( r2_lattice3(sK1,X0,k1_yellow_0(sK1,X0)) ),
% 1.08/0.99      inference(global_propositional_subsumption,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_436,c_16]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_825,plain,
% 1.08/0.99      ( r2_lattice3(sK1,X0_51,k1_yellow_0(sK1,X0_51)) ),
% 1.08/0.99      inference(subtyping,[status(esa)],[c_440]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1099,plain,
% 1.08/0.99      ( r2_lattice3(sK1,sK3,k1_yellow_0(sK1,sK3)) ),
% 1.08/0.99      inference(instantiation,[status(thm)],[c_825]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_12,plain,
% 1.08/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.08/0.99      | r2_lattice3(X0,X3,X2)
% 1.08/0.99      | ~ r1_tarski(X3,X1)
% 1.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_15,negated_conjecture,
% 1.08/0.99      ( r1_tarski(sK2,sK3) ),
% 1.08/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_306,plain,
% 1.08/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.08/0.99      | r2_lattice3(X0,X3,X2)
% 1.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.99      | ~ l1_orders_2(X0)
% 1.08/0.99      | sK2 != X3
% 1.08/0.99      | sK3 != X1 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_307,plain,
% 1.08/0.99      ( r2_lattice3(X0,sK2,X1)
% 1.08/0.99      | ~ r2_lattice3(X0,sK3,X1)
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_543,plain,
% 1.08/0.99      ( r2_lattice3(X0,sK2,X1)
% 1.08/0.99      | ~ r2_lattice3(X0,sK3,X1)
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.08/0.99      | sK1 != X0 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_307,c_16]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_544,plain,
% 1.08/0.99      ( r2_lattice3(sK1,sK2,X0)
% 1.08/0.99      | ~ r2_lattice3(sK1,sK3,X0)
% 1.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_543]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_821,plain,
% 1.08/0.99      ( r2_lattice3(sK1,sK2,X0_50)
% 1.08/0.99      | ~ r2_lattice3(sK1,sK3,X0_50)
% 1.08/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK1)) ),
% 1.08/0.99      inference(subtyping,[status(esa)],[c_544]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1098,plain,
% 1.08/0.99      ( r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
% 1.08/0.99      | ~ r2_lattice3(sK1,sK3,k1_yellow_0(sK1,sK3))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(instantiation,[status(thm)],[c_821]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_570,plain,
% 1.08/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK1 != X0 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_571,plain,
% 1.08/0.99      ( m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_570]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_819,plain,
% 1.08/0.99      ( m1_subset_1(k1_yellow_0(sK1,X0_51),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(subtyping,[status(esa)],[c_571]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1095,plain,
% 1.08/0.99      ( m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(instantiation,[status(thm)],[c_819]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_11,plain,
% 1.08/0.99      ( r1_orders_2(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
% 1.08/0.99      | ~ r1_tarski(X2,X1)
% 1.08/0.99      | ~ r2_yellow_0(X0,X1)
% 1.08/0.99      | ~ r2_yellow_0(X0,X2)
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_288,plain,
% 1.08/0.99      ( r1_orders_2(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
% 1.08/0.99      | ~ r2_yellow_0(X0,X2)
% 1.08/0.99      | ~ r2_yellow_0(X0,X1)
% 1.08/0.99      | ~ l1_orders_2(X0)
% 1.08/0.99      | sK2 != X2
% 1.08/0.99      | sK3 != X1 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_289,plain,
% 1.08/0.99      ( r1_orders_2(X0,k2_yellow_0(X0,sK3),k2_yellow_0(X0,sK2))
% 1.08/0.99      | ~ r2_yellow_0(X0,sK2)
% 1.08/0.99      | ~ r2_yellow_0(X0,sK3)
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_288]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_558,plain,
% 1.08/0.99      ( r1_orders_2(X0,k2_yellow_0(X0,sK3),k2_yellow_0(X0,sK2))
% 1.08/0.99      | ~ r2_yellow_0(X0,sK2)
% 1.08/0.99      | ~ r2_yellow_0(X0,sK3)
% 1.08/0.99      | sK1 != X0 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_289,c_16]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_559,plain,
% 1.08/0.99      ( r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
% 1.08/0.99      | ~ r2_yellow_0(sK1,sK2)
% 1.08/0.99      | ~ r2_yellow_0(sK1,sK3) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_558]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_9,plain,
% 1.08/0.99      ( r2_yellow_0(X0,X1)
% 1.08/0.99      | ~ v5_orders_2(X0)
% 1.08/0.99      | ~ v3_lattice3(X0)
% 1.08/0.99      | v2_struct_0(X0)
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_269,plain,
% 1.08/0.99      ( r2_yellow_0(X0,X1)
% 1.08/0.99      | ~ v5_orders_2(X0)
% 1.08/0.99      | v2_struct_0(X0)
% 1.08/0.99      | ~ l1_orders_2(X0)
% 1.08/0.99      | sK1 != X0 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_270,plain,
% 1.08/0.99      ( r2_yellow_0(sK1,X0)
% 1.08/0.99      | ~ v5_orders_2(sK1)
% 1.08/0.99      | v2_struct_0(sK1)
% 1.08/0.99      | ~ l1_orders_2(sK1) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_269]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_274,plain,
% 1.08/0.99      ( r2_yellow_0(sK1,X0) ),
% 1.08/0.99      inference(global_propositional_subsumption,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_270,c_19,c_18,c_16,c_58]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_567,plain,
% 1.08/0.99      ( r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2)) ),
% 1.08/0.99      inference(forward_subsumption_resolution,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_559,c_274,c_274]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_14,negated_conjecture,
% 1.08/0.99      ( ~ r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
% 1.08/0.99      | ~ r3_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) ),
% 1.08/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_0,plain,
% 1.08/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 1.08/0.99      | r3_orders_2(X0,X1,X2)
% 1.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.08/0.99      | v2_struct_0(X0)
% 1.08/0.99      | ~ v3_orders_2(X0)
% 1.08/0.99      | ~ l1_orders_2(X0) ),
% 1.08/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_20,negated_conjecture,
% 1.08/0.99      ( v3_orders_2(sK1) ),
% 1.08/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_358,plain,
% 1.08/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 1.08/0.99      | r3_orders_2(X0,X1,X2)
% 1.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.08/0.99      | v2_struct_0(X0)
% 1.08/0.99      | ~ l1_orders_2(X0)
% 1.08/0.99      | sK1 != X0 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_359,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 1.08/0.99      | r3_orders_2(sK1,X0,X1)
% 1.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.08/0.99      | v2_struct_0(sK1)
% 1.08/0.99      | ~ l1_orders_2(sK1) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_363,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 1.08/0.99      | r3_orders_2(sK1,X0,X1)
% 1.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.08/0.99      inference(global_propositional_subsumption,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_359,c_18,c_16,c_58]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_364,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 1.08/0.99      | r3_orders_2(sK1,X0,X1)
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.08/0.99      inference(renaming,[status(thm)],[c_363]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_393,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 1.08/0.99      | ~ r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
% 1.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.08/0.99      | k1_yellow_0(sK1,sK2) != X0
% 1.08/0.99      | k1_yellow_0(sK1,sK3) != X1
% 1.08/0.99      | sK1 != sK1 ),
% 1.08/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_364]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_394,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,k2_yellow_0(sK1,sK3),k2_yellow_0(sK1,sK2))
% 1.08/0.99      | ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,sK2),u1_struct_0(sK1))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(unflattening,[status(thm)],[c_393]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_584,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,sK2),u1_struct_0(sK1))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(backward_subsumption_resolution,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_567,c_394]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_588,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(backward_subsumption_resolution,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_571,c_584]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_818,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3))
% 1.08/0.99      | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
% 1.08/0.99      inference(subtyping,[status(esa)],[c_588]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1027,plain,
% 1.08/0.99      ( r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) != iProver_top
% 1.08/0.99      | m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
% 1.08/0.99      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1026,plain,
% 1.08/0.99      ( m1_subset_1(k1_yellow_0(sK1,X0_51),u1_struct_0(sK1)) = iProver_top ),
% 1.08/0.99      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1036,plain,
% 1.08/0.99      ( r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) != iProver_top ),
% 1.08/0.99      inference(forward_subsumption_resolution,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_1027,c_1026]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(c_1077,plain,
% 1.08/0.99      ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) ),
% 1.08/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1036]) ).
% 1.08/0.99  
% 1.08/0.99  cnf(contradiction,plain,
% 1.08/0.99      ( $false ),
% 1.08/0.99      inference(minisat,
% 1.08/0.99                [status(thm)],
% 1.08/0.99                [c_1174,c_1099,c_1098,c_1095,c_1077]) ).
% 1.08/0.99  
% 1.08/0.99  
% 1.08/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.08/0.99  
% 1.08/0.99  ------                               Statistics
% 1.08/0.99  
% 1.08/0.99  ------ General
% 1.08/0.99  
% 1.08/0.99  abstr_ref_over_cycles:                  0
% 1.08/0.99  abstr_ref_under_cycles:                 0
% 1.08/0.99  gc_basic_clause_elim:                   0
% 1.08/0.99  forced_gc_time:                         0
% 1.08/0.99  parsing_time:                           0.012
% 1.08/0.99  unif_index_cands_time:                  0.
% 1.08/0.99  unif_index_add_time:                    0.
% 1.08/0.99  orderings_time:                         0.
% 1.08/0.99  out_proof_time:                         0.009
% 1.08/0.99  total_time:                             0.07
% 1.08/0.99  num_of_symbols:                         53
% 1.08/0.99  num_of_terms:                           1032
% 1.08/0.99  
% 1.08/0.99  ------ Preprocessing
% 1.08/0.99  
% 1.08/0.99  num_of_splits:                          0
% 1.08/0.99  num_of_split_atoms:                     0
% 1.08/0.99  num_of_reused_defs:                     0
% 1.08/0.99  num_eq_ax_congr_red:                    28
% 1.08/0.99  num_of_sem_filtered_clauses:            2
% 1.08/0.99  num_of_subtypes:                        4
% 1.08/0.99  monotx_restored_types:                  0
% 1.08/0.99  sat_num_of_epr_types:                   0
% 1.08/0.99  sat_num_of_non_cyclic_types:            0
% 1.08/0.99  sat_guarded_non_collapsed_types:        1
% 1.08/0.99  num_pure_diseq_elim:                    0
% 1.08/0.99  simp_replaced_by:                       0
% 1.08/0.99  res_preprocessed:                       59
% 1.08/0.99  prep_upred:                             0
% 1.08/0.99  prep_unflattend:                        32
% 1.08/0.99  smt_new_axioms:                         0
% 1.08/0.99  pred_elim_cands:                        3
% 1.08/0.99  pred_elim:                              10
% 1.08/0.99  pred_elim_cl:                           11
% 1.08/0.99  pred_elim_cycles:                       12
% 1.08/0.99  merged_defs:                            0
% 1.08/0.99  merged_defs_ncl:                        0
% 1.08/0.99  bin_hyper_res:                          0
% 1.08/0.99  prep_cycles:                            4
% 1.08/0.99  pred_elim_time:                         0.009
% 1.08/0.99  splitting_time:                         0.
% 1.08/0.99  sem_filter_time:                        0.
% 1.08/0.99  monotx_time:                            0.
% 1.08/0.99  subtype_inf_time:                       0.
% 1.08/0.99  
% 1.08/0.99  ------ Problem properties
% 1.08/0.99  
% 1.08/0.99  clauses:                                9
% 1.08/0.99  conjectures:                            0
% 1.08/0.99  epr:                                    0
% 1.08/0.99  horn:                                   7
% 1.08/0.99  ground:                                 2
% 1.08/0.99  unary:                                  3
% 1.08/0.99  binary:                                 1
% 1.08/0.99  lits:                                   23
% 1.08/0.99  lits_eq:                                3
% 1.08/0.99  fd_pure:                                0
% 1.08/0.99  fd_pseudo:                              0
% 1.08/0.99  fd_cond:                                0
% 1.08/0.99  fd_pseudo_cond:                         3
% 1.08/0.99  ac_symbols:                             0
% 1.08/0.99  
% 1.08/0.99  ------ Propositional Solver
% 1.08/0.99  
% 1.08/0.99  prop_solver_calls:                      23
% 1.08/0.99  prop_fast_solver_calls:                 502
% 1.08/0.99  smt_solver_calls:                       0
% 1.08/0.99  smt_fast_solver_calls:                  0
% 1.08/0.99  prop_num_of_clauses:                    289
% 1.08/0.99  prop_preprocess_simplified:             1697
% 1.08/0.99  prop_fo_subsumed:                       22
% 1.08/0.99  prop_solver_time:                       0.
% 1.08/0.99  smt_solver_time:                        0.
% 1.08/0.99  smt_fast_solver_time:                   0.
% 1.08/0.99  prop_fast_solver_time:                  0.
% 1.08/0.99  prop_unsat_core_time:                   0.
% 1.08/0.99  
% 1.08/0.99  ------ QBF
% 1.08/0.99  
% 1.08/0.99  qbf_q_res:                              0
% 1.08/0.99  qbf_num_tautologies:                    0
% 1.08/0.99  qbf_prep_cycles:                        0
% 1.08/0.99  
% 1.08/0.99  ------ BMC1
% 1.08/0.99  
% 1.08/0.99  bmc1_current_bound:                     -1
% 1.08/0.99  bmc1_last_solved_bound:                 -1
% 1.08/0.99  bmc1_unsat_core_size:                   -1
% 1.08/0.99  bmc1_unsat_core_parents_size:           -1
% 1.08/0.99  bmc1_merge_next_fun:                    0
% 1.08/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.08/0.99  
% 1.08/0.99  ------ Instantiation
% 1.08/0.99  
% 1.08/0.99  inst_num_of_clauses:                    29
% 1.08/0.99  inst_num_in_passive:                    4
% 1.08/0.99  inst_num_in_active:                     19
% 1.08/0.99  inst_num_in_unprocessed:                5
% 1.08/0.99  inst_num_of_loops:                      22
% 1.08/0.99  inst_num_of_learning_restarts:          0
% 1.08/0.99  inst_num_moves_active_passive:          1
% 1.08/0.99  inst_lit_activity:                      0
% 1.08/0.99  inst_lit_activity_moves:                0
% 1.08/0.99  inst_num_tautologies:                   0
% 1.08/0.99  inst_num_prop_implied:                  0
% 1.08/0.99  inst_num_existing_simplified:           0
% 1.08/0.99  inst_num_eq_res_simplified:             0
% 1.08/0.99  inst_num_child_elim:                    0
% 1.08/0.99  inst_num_of_dismatching_blockings:      6
% 1.08/0.99  inst_num_of_non_proper_insts:           16
% 1.08/0.99  inst_num_of_duplicates:                 0
% 1.08/0.99  inst_inst_num_from_inst_to_res:         0
% 1.08/0.99  inst_dismatching_checking_time:         0.
% 1.08/0.99  
% 1.08/0.99  ------ Resolution
% 1.08/0.99  
% 1.08/0.99  res_num_of_clauses:                     0
% 1.08/0.99  res_num_in_passive:                     0
% 1.08/0.99  res_num_in_active:                      0
% 1.08/0.99  res_num_of_loops:                       63
% 1.08/0.99  res_forward_subset_subsumed:            1
% 1.08/0.99  res_backward_subset_subsumed:           0
% 1.08/0.99  res_forward_subsumed:                   0
% 1.08/0.99  res_backward_subsumed:                  0
% 1.08/0.99  res_forward_subsumption_resolution:     4
% 1.08/0.99  res_backward_subsumption_resolution:    2
% 1.08/0.99  res_clause_to_clause_subsumption:       39
% 1.08/0.99  res_orphan_elimination:                 0
% 1.08/0.99  res_tautology_del:                      1
% 1.08/0.99  res_num_eq_res_simplified:              0
% 1.08/0.99  res_num_sel_changes:                    0
% 1.08/0.99  res_moves_from_active_to_pass:          0
% 1.08/0.99  
% 1.08/0.99  ------ Superposition
% 1.08/0.99  
% 1.08/0.99  sup_time_total:                         0.
% 1.08/0.99  sup_time_generating:                    0.
% 1.08/0.99  sup_time_sim_full:                      0.
% 1.08/0.99  sup_time_sim_immed:                     0.
% 1.08/0.99  
% 1.08/0.99  sup_num_of_clauses:                     10
% 1.08/0.99  sup_num_in_active:                      4
% 1.08/0.99  sup_num_in_passive:                     6
% 1.08/0.99  sup_num_of_loops:                       4
% 1.08/0.99  sup_fw_superposition:                   1
% 1.08/0.99  sup_bw_superposition:                   0
% 1.08/0.99  sup_immediate_simplified:               0
% 1.08/0.99  sup_given_eliminated:                   0
% 1.08/0.99  comparisons_done:                       0
% 1.08/0.99  comparisons_avoided:                    0
% 1.08/0.99  
% 1.08/0.99  ------ Simplifications
% 1.08/0.99  
% 1.08/0.99  
% 1.08/0.99  sim_fw_subset_subsumed:                 0
% 1.08/0.99  sim_bw_subset_subsumed:                 0
% 1.08/0.99  sim_fw_subsumed:                        0
% 1.08/0.99  sim_bw_subsumed:                        0
% 1.08/0.99  sim_fw_subsumption_res:                 1
% 1.08/0.99  sim_bw_subsumption_res:                 0
% 1.08/0.99  sim_tautology_del:                      0
% 1.08/0.99  sim_eq_tautology_del:                   0
% 1.08/0.99  sim_eq_res_simp:                        0
% 1.08/0.99  sim_fw_demodulated:                     0
% 1.08/0.99  sim_bw_demodulated:                     0
% 1.08/0.99  sim_light_normalised:                   0
% 1.08/0.99  sim_joinable_taut:                      0
% 1.08/0.99  sim_joinable_simp:                      0
% 1.08/0.99  sim_ac_normalised:                      0
% 1.08/0.99  sim_smt_subsumption:                    0
% 1.08/0.99  
%------------------------------------------------------------------------------
