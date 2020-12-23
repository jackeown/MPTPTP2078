%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:21 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 611 expanded)
%              Number of clauses        :   81 ( 138 expanded)
%              Number of leaves         :   15 ( 135 expanded)
%              Depth                    :   19
%              Number of atoms          :  831 (4109 expanded)
%              Number of equality atoms :   55 (  81 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = X1
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | ~ r1_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = X1
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | ~ r1_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = X1
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
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = X1
                | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,sK5),k2_yellow_0(X0,sK4))
          | ~ r3_orders_2(X0,k1_yellow_0(X0,sK4),k1_yellow_0(X0,sK5)) )
        & r1_tarski(sK4,sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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
          ( ( ~ r1_orders_2(sK3,k2_yellow_0(sK3,X2),k2_yellow_0(sK3,X1))
            | ~ r3_orders_2(sK3,k1_yellow_0(sK3,X1),k1_yellow_0(sK3,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK3)
      & v3_lattice3(sK3)
      & v1_lattice3(sK3)
      & v5_orders_2(sK3)
      & v3_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
      | ~ r3_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5)) )
    & r1_tarski(sK4,sK5)
    & l1_orders_2(sK3)
    & v3_lattice3(sK3)
    & v1_lattice3(sK3)
    & v5_orders_2(sK3)
    & v3_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f31,f49,f48])).

fof(f76,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v3_lattice3(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k1_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X2,X3)
                     => r1_orders_2(X0,X1,X3) ) )
                & r2_lattice3(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = X1
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = X1
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = X1
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
        & r2_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = X1
                | ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,X1)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : r2_yellow_0(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK0(X0,X1,X2))
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,
    ( ~ r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
    | ~ r3_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5)) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_9,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_179,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_9])).

cnf(c_180,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_2,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_367,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_27])).

cnf(c_368,plain,
    ( ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_94,plain,
    ( ~ v1_lattice3(sK3)
    | ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_370,plain,
    ( ~ v2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_27,c_25,c_94])).

cnf(c_730,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_180,c_370])).

cnf(c_731,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,X1,k2_yellow_0(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ v3_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( v3_lattice3(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r1_orders_2(sK3,X1,k2_yellow_0(sK3,X0))
    | ~ r1_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_28,c_26,c_25])).

cnf(c_736,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,X1,k2_yellow_0(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_1162,plain,
    ( ~ r1_lattice3(sK3,X0_52,X0_51)
    | r1_orders_2(sK3,X0_51,k2_yellow_0(sK3,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_736])).

cnf(c_1707,plain,
    ( ~ r1_lattice3(sK3,X0_52,k2_yellow_0(sK3,X1_52))
    | r1_orders_2(sK3,k2_yellow_0(sK3,X1_52),k2_yellow_0(sK3,X0_52))
    | ~ m1_subset_1(k2_yellow_0(sK3,X1_52),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_2002,plain,
    ( ~ r1_lattice3(sK3,sK4,k2_yellow_0(sK3,sK5))
    | r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_8,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_8])).

cnf(c_197,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_694,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_197,c_370])).

cnf(c_695,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,k1_yellow_0(sK3,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ v3_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r1_orders_2(sK3,k1_yellow_0(sK3,X0),X1)
    | ~ r2_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_28,c_26,c_25])).

cnf(c_700,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,k1_yellow_0(sK3,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_1164,plain,
    ( ~ r2_lattice3(sK3,X0_52,X0_51)
    | r1_orders_2(sK3,k1_yellow_0(sK3,X0_52),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_700])).

cnf(c_1712,plain,
    ( ~ r2_lattice3(sK3,X0_52,k1_yellow_0(sK3,X1_52))
    | r1_orders_2(sK3,k1_yellow_0(sK3,X0_52),k1_yellow_0(sK3,X1_52))
    | ~ m1_subset_1(k1_yellow_0(sK3,X1_52),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1922,plain,
    ( ~ r2_lattice3(sK3,sK4,k1_yellow_0(sK3,sK5))
    | r1_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5))
    | ~ m1_subset_1(k1_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1712])).

cnf(c_997,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_998,plain,
    ( m1_subset_1(k2_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_997])).

cnf(c_1152,plain,
    ( m1_subset_1(k2_yellow_0(sK3,X0_52),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_998])).

cnf(c_1890,plain,
    ( m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_15,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_189,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_8])).

cnf(c_715,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_189,c_370])).

cnf(c_716,plain,
    ( r2_lattice3(sK3,X0,k1_yellow_0(sK3,X0))
    | ~ v5_orders_2(sK3)
    | ~ v3_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_720,plain,
    ( r2_lattice3(sK3,X0,k1_yellow_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_28,c_26,c_25])).

cnf(c_1163,plain,
    ( r2_lattice3(sK3,X0_52,k1_yellow_0(sK3,X0_52)) ),
    inference(subtyping,[status(esa)],[c_720])).

cnf(c_1697,plain,
    ( r2_lattice3(sK3,sK5,k1_yellow_0(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_21,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_398,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_399,plain,
    ( r2_lattice3(X0,sK4,X1)
    | ~ r2_lattice3(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_967,plain,
    ( r2_lattice3(X0,sK4,X1)
    | ~ r2_lattice3(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_399,c_25])).

cnf(c_968,plain,
    ( r2_lattice3(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_1154,plain,
    ( r2_lattice3(sK3,sK4,X0_51)
    | ~ r2_lattice3(sK3,sK5,X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_968])).

cnf(c_1696,plain,
    ( r2_lattice3(sK3,sK4,k1_yellow_0(sK3,sK5))
    | ~ r2_lattice3(sK3,sK5,k1_yellow_0(sK3,sK5))
    | ~ m1_subset_1(k1_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_20,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10,plain,
    ( r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_172,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_10,c_9,c_7])).

cnf(c_751,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_370])).

cnf(c_752,plain,
    ( r1_lattice3(sK3,X0,k2_yellow_0(sK3,X0))
    | ~ v5_orders_2(sK3)
    | ~ v3_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_756,plain,
    ( r1_lattice3(sK3,X0,k2_yellow_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_752,c_28,c_26,c_25])).

cnf(c_1161,plain,
    ( r1_lattice3(sK3,X0_52,k2_yellow_0(sK3,X0_52)) ),
    inference(subtyping,[status(esa)],[c_756])).

cnf(c_1691,plain,
    ( r1_lattice3(sK3,sK5,k2_yellow_0(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_22,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_380,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_24])).

cnf(c_381,plain,
    ( r1_lattice3(X0,sK4,X1)
    | ~ r1_lattice3(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_982,plain,
    ( r1_lattice3(X0,sK4,X1)
    | ~ r1_lattice3(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_25])).

cnf(c_983,plain,
    ( r1_lattice3(sK3,sK4,X0)
    | ~ r1_lattice3(sK3,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_1153,plain,
    ( r1_lattice3(sK3,sK4,X0_51)
    | ~ r1_lattice3(sK3,sK5,X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_983])).

cnf(c_1690,plain,
    ( r1_lattice3(sK3,sK4,k2_yellow_0(sK3,sK5))
    | ~ r1_lattice3(sK3,sK5,k2_yellow_0(sK3,sK5))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1006,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_1007,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(c_1151,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0_52),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1007])).

cnf(c_1687,plain,
    ( m1_subset_1(k1_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_1230,plain,
    ( m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_23,negated_conjecture,
    ( ~ r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
    | ~ r3_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_450,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_29])).

cnf(c_451,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_455,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_27,c_25,c_94])).

cnf(c_456,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_455])).

cnf(c_485,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k1_yellow_0(sK3,sK4) != X0
    | k1_yellow_0(sK3,sK5) != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_456])).

cnf(c_486,plain,
    ( ~ r1_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k1_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2002,c_1922,c_1890,c_1697,c_1696,c_1691,c_1690,c_1687,c_1230,c_486])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.33/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.33/0.97  
% 1.33/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.33/0.97  
% 1.33/0.97  ------  iProver source info
% 1.33/0.97  
% 1.33/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.33/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.33/0.97  git: non_committed_changes: false
% 1.33/0.97  git: last_make_outside_of_git: false
% 1.33/0.97  
% 1.33/0.97  ------ 
% 1.33/0.97  
% 1.33/0.97  ------ Input Options
% 1.33/0.97  
% 1.33/0.97  --out_options                           all
% 1.33/0.97  --tptp_safe_out                         true
% 1.33/0.97  --problem_path                          ""
% 1.33/0.97  --include_path                          ""
% 1.33/0.97  --clausifier                            res/vclausify_rel
% 1.33/0.97  --clausifier_options                    --mode clausify
% 1.33/0.97  --stdin                                 false
% 1.33/0.97  --stats_out                             all
% 1.33/0.97  
% 1.33/0.97  ------ General Options
% 1.33/0.97  
% 1.33/0.97  --fof                                   false
% 1.33/0.97  --time_out_real                         305.
% 1.33/0.97  --time_out_virtual                      -1.
% 1.33/0.97  --symbol_type_check                     false
% 1.33/0.97  --clausify_out                          false
% 1.33/0.97  --sig_cnt_out                           false
% 1.33/0.97  --trig_cnt_out                          false
% 1.33/0.97  --trig_cnt_out_tolerance                1.
% 1.33/0.97  --trig_cnt_out_sk_spl                   false
% 1.33/0.97  --abstr_cl_out                          false
% 1.33/0.97  
% 1.33/0.97  ------ Global Options
% 1.33/0.97  
% 1.33/0.97  --schedule                              default
% 1.33/0.97  --add_important_lit                     false
% 1.33/0.97  --prop_solver_per_cl                    1000
% 1.33/0.97  --min_unsat_core                        false
% 1.33/0.97  --soft_assumptions                      false
% 1.33/0.97  --soft_lemma_size                       3
% 1.33/0.97  --prop_impl_unit_size                   0
% 1.33/0.97  --prop_impl_unit                        []
% 1.33/0.97  --share_sel_clauses                     true
% 1.33/0.97  --reset_solvers                         false
% 1.33/0.97  --bc_imp_inh                            [conj_cone]
% 1.33/0.97  --conj_cone_tolerance                   3.
% 1.33/0.97  --extra_neg_conj                        none
% 1.33/0.97  --large_theory_mode                     true
% 1.33/0.97  --prolific_symb_bound                   200
% 1.33/0.97  --lt_threshold                          2000
% 1.33/0.97  --clause_weak_htbl                      true
% 1.33/0.97  --gc_record_bc_elim                     false
% 1.33/0.97  
% 1.33/0.97  ------ Preprocessing Options
% 1.33/0.97  
% 1.33/0.97  --preprocessing_flag                    true
% 1.33/0.97  --time_out_prep_mult                    0.1
% 1.33/0.97  --splitting_mode                        input
% 1.33/0.97  --splitting_grd                         true
% 1.33/0.97  --splitting_cvd                         false
% 1.33/0.97  --splitting_cvd_svl                     false
% 1.33/0.97  --splitting_nvd                         32
% 1.33/0.97  --sub_typing                            true
% 1.33/0.97  --prep_gs_sim                           true
% 1.33/0.97  --prep_unflatten                        true
% 1.33/0.97  --prep_res_sim                          true
% 1.33/0.97  --prep_upred                            true
% 1.33/0.97  --prep_sem_filter                       exhaustive
% 1.33/0.97  --prep_sem_filter_out                   false
% 1.33/0.97  --pred_elim                             true
% 1.33/0.97  --res_sim_input                         true
% 1.33/0.97  --eq_ax_congr_red                       true
% 1.33/0.97  --pure_diseq_elim                       true
% 1.33/0.97  --brand_transform                       false
% 1.33/0.97  --non_eq_to_eq                          false
% 1.33/0.97  --prep_def_merge                        true
% 1.33/0.97  --prep_def_merge_prop_impl              false
% 1.33/0.97  --prep_def_merge_mbd                    true
% 1.33/0.97  --prep_def_merge_tr_red                 false
% 1.33/0.97  --prep_def_merge_tr_cl                  false
% 1.33/0.97  --smt_preprocessing                     true
% 1.33/0.97  --smt_ac_axioms                         fast
% 1.33/0.97  --preprocessed_out                      false
% 1.33/0.97  --preprocessed_stats                    false
% 1.33/0.97  
% 1.33/0.97  ------ Abstraction refinement Options
% 1.33/0.97  
% 1.33/0.97  --abstr_ref                             []
% 1.33/0.97  --abstr_ref_prep                        false
% 1.33/0.97  --abstr_ref_until_sat                   false
% 1.33/0.97  --abstr_ref_sig_restrict                funpre
% 1.33/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/0.97  --abstr_ref_under                       []
% 1.33/0.97  
% 1.33/0.97  ------ SAT Options
% 1.33/0.97  
% 1.33/0.97  --sat_mode                              false
% 1.33/0.97  --sat_fm_restart_options                ""
% 1.33/0.97  --sat_gr_def                            false
% 1.33/0.97  --sat_epr_types                         true
% 1.33/0.97  --sat_non_cyclic_types                  false
% 1.33/0.97  --sat_finite_models                     false
% 1.33/0.97  --sat_fm_lemmas                         false
% 1.33/0.97  --sat_fm_prep                           false
% 1.33/0.97  --sat_fm_uc_incr                        true
% 1.33/0.97  --sat_out_model                         small
% 1.33/0.97  --sat_out_clauses                       false
% 1.33/0.97  
% 1.33/0.97  ------ QBF Options
% 1.33/0.97  
% 1.33/0.97  --qbf_mode                              false
% 1.33/0.97  --qbf_elim_univ                         false
% 1.33/0.97  --qbf_dom_inst                          none
% 1.33/0.97  --qbf_dom_pre_inst                      false
% 1.33/0.97  --qbf_sk_in                             false
% 1.33/0.97  --qbf_pred_elim                         true
% 1.33/0.97  --qbf_split                             512
% 1.33/0.97  
% 1.33/0.97  ------ BMC1 Options
% 1.33/0.97  
% 1.33/0.97  --bmc1_incremental                      false
% 1.33/0.97  --bmc1_axioms                           reachable_all
% 1.33/0.97  --bmc1_min_bound                        0
% 1.33/0.97  --bmc1_max_bound                        -1
% 1.33/0.97  --bmc1_max_bound_default                -1
% 1.33/0.97  --bmc1_symbol_reachability              true
% 1.33/0.97  --bmc1_property_lemmas                  false
% 1.33/0.97  --bmc1_k_induction                      false
% 1.33/0.97  --bmc1_non_equiv_states                 false
% 1.33/0.97  --bmc1_deadlock                         false
% 1.33/0.97  --bmc1_ucm                              false
% 1.33/0.97  --bmc1_add_unsat_core                   none
% 1.33/0.97  --bmc1_unsat_core_children              false
% 1.33/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/0.97  --bmc1_out_stat                         full
% 1.33/0.97  --bmc1_ground_init                      false
% 1.33/0.97  --bmc1_pre_inst_next_state              false
% 1.33/0.97  --bmc1_pre_inst_state                   false
% 1.33/0.97  --bmc1_pre_inst_reach_state             false
% 1.33/0.97  --bmc1_out_unsat_core                   false
% 1.33/0.97  --bmc1_aig_witness_out                  false
% 1.33/0.97  --bmc1_verbose                          false
% 1.33/0.97  --bmc1_dump_clauses_tptp                false
% 1.33/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.33/0.97  --bmc1_dump_file                        -
% 1.33/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.33/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.33/0.97  --bmc1_ucm_extend_mode                  1
% 1.33/0.97  --bmc1_ucm_init_mode                    2
% 1.33/0.97  --bmc1_ucm_cone_mode                    none
% 1.33/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.33/0.97  --bmc1_ucm_relax_model                  4
% 1.33/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.33/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/0.97  --bmc1_ucm_layered_model                none
% 1.33/0.97  --bmc1_ucm_max_lemma_size               10
% 1.33/0.97  
% 1.33/0.97  ------ AIG Options
% 1.33/0.97  
% 1.33/0.97  --aig_mode                              false
% 1.33/0.97  
% 1.33/0.97  ------ Instantiation Options
% 1.33/0.97  
% 1.33/0.97  --instantiation_flag                    true
% 1.33/0.97  --inst_sos_flag                         false
% 1.33/0.97  --inst_sos_phase                        true
% 1.33/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/0.97  --inst_lit_sel_side                     num_symb
% 1.33/0.97  --inst_solver_per_active                1400
% 1.33/0.97  --inst_solver_calls_frac                1.
% 1.33/0.97  --inst_passive_queue_type               priority_queues
% 1.33/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.33/0.97  --inst_passive_queues_freq              [25;2]
% 1.33/0.97  --inst_dismatching                      true
% 1.33/0.97  --inst_eager_unprocessed_to_passive     true
% 1.33/0.97  --inst_prop_sim_given                   true
% 1.33/0.97  --inst_prop_sim_new                     false
% 1.33/0.97  --inst_subs_new                         false
% 1.33/0.97  --inst_eq_res_simp                      false
% 1.33/0.97  --inst_subs_given                       false
% 1.33/0.97  --inst_orphan_elimination               true
% 1.33/0.97  --inst_learning_loop_flag               true
% 1.33/0.97  --inst_learning_start                   3000
% 1.33/0.97  --inst_learning_factor                  2
% 1.33/0.97  --inst_start_prop_sim_after_learn       3
% 1.33/0.97  --inst_sel_renew                        solver
% 1.33/0.97  --inst_lit_activity_flag                true
% 1.33/0.97  --inst_restr_to_given                   false
% 1.33/0.97  --inst_activity_threshold               500
% 1.33/0.97  --inst_out_proof                        true
% 1.33/0.97  
% 1.33/0.97  ------ Resolution Options
% 1.33/0.97  
% 1.33/0.97  --resolution_flag                       true
% 1.33/0.97  --res_lit_sel                           adaptive
% 1.33/0.97  --res_lit_sel_side                      none
% 1.33/0.97  --res_ordering                          kbo
% 1.33/0.97  --res_to_prop_solver                    active
% 1.33/0.97  --res_prop_simpl_new                    false
% 1.33/0.97  --res_prop_simpl_given                  true
% 1.33/0.97  --res_passive_queue_type                priority_queues
% 1.33/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.33/0.97  --res_passive_queues_freq               [15;5]
% 1.33/0.97  --res_forward_subs                      full
% 1.33/0.97  --res_backward_subs                     full
% 1.33/0.97  --res_forward_subs_resolution           true
% 1.33/0.97  --res_backward_subs_resolution          true
% 1.33/0.97  --res_orphan_elimination                true
% 1.33/0.97  --res_time_limit                        2.
% 1.33/0.97  --res_out_proof                         true
% 1.33/0.97  
% 1.33/0.97  ------ Superposition Options
% 1.33/0.97  
% 1.33/0.97  --superposition_flag                    true
% 1.33/0.97  --sup_passive_queue_type                priority_queues
% 1.33/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.33/0.97  --demod_completeness_check              fast
% 1.33/0.97  --demod_use_ground                      true
% 1.33/0.97  --sup_to_prop_solver                    passive
% 1.33/0.97  --sup_prop_simpl_new                    true
% 1.33/0.97  --sup_prop_simpl_given                  true
% 1.33/0.97  --sup_fun_splitting                     false
% 1.33/0.97  --sup_smt_interval                      50000
% 1.33/0.97  
% 1.33/0.97  ------ Superposition Simplification Setup
% 1.33/0.97  
% 1.33/0.97  --sup_indices_passive                   []
% 1.33/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.97  --sup_full_bw                           [BwDemod]
% 1.33/0.97  --sup_immed_triv                        [TrivRules]
% 1.33/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.97  --sup_immed_bw_main                     []
% 1.33/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.97  
% 1.33/0.97  ------ Combination Options
% 1.33/0.97  
% 1.33/0.97  --comb_res_mult                         3
% 1.33/0.97  --comb_sup_mult                         2
% 1.33/0.97  --comb_inst_mult                        10
% 1.33/0.97  
% 1.33/0.97  ------ Debug Options
% 1.33/0.97  
% 1.33/0.97  --dbg_backtrace                         false
% 1.33/0.97  --dbg_dump_prop_clauses                 false
% 1.33/0.97  --dbg_dump_prop_clauses_file            -
% 1.33/0.97  --dbg_out_stat                          false
% 1.33/0.97  ------ Parsing...
% 1.33/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.33/0.97  
% 1.33/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.33/0.97  
% 1.33/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.33/0.97  
% 1.33/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.33/0.97  ------ Proving...
% 1.33/0.97  ------ Problem Properties 
% 1.33/0.97  
% 1.33/0.97  
% 1.33/0.97  clauses                                 18
% 1.33/0.97  conjectures                             0
% 1.33/0.97  EPR                                     0
% 1.33/0.97  Horn                                    12
% 1.33/0.97  unary                                   4
% 1.33/0.97  binary                                  0
% 1.33/0.97  lits                                    55
% 1.33/0.97  lits eq                                 9
% 1.33/0.97  fd_pure                                 0
% 1.33/0.97  fd_pseudo                               0
% 1.33/0.97  fd_cond                                 0
% 1.33/0.97  fd_pseudo_cond                          9
% 1.33/0.97  AC symbols                              0
% 1.33/0.97  
% 1.33/0.97  ------ Schedule dynamic 5 is on 
% 1.33/0.97  
% 1.33/0.97  ------ no conjectures: strip conj schedule 
% 1.33/0.97  
% 1.33/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.33/0.97  
% 1.33/0.97  
% 1.33/0.97  ------ 
% 1.33/0.97  Current options:
% 1.33/0.97  ------ 
% 1.33/0.97  
% 1.33/0.97  ------ Input Options
% 1.33/0.97  
% 1.33/0.97  --out_options                           all
% 1.33/0.97  --tptp_safe_out                         true
% 1.33/0.97  --problem_path                          ""
% 1.33/0.97  --include_path                          ""
% 1.33/0.97  --clausifier                            res/vclausify_rel
% 1.33/0.97  --clausifier_options                    --mode clausify
% 1.33/0.97  --stdin                                 false
% 1.33/0.97  --stats_out                             all
% 1.33/0.97  
% 1.33/0.97  ------ General Options
% 1.33/0.97  
% 1.33/0.97  --fof                                   false
% 1.33/0.97  --time_out_real                         305.
% 1.33/0.97  --time_out_virtual                      -1.
% 1.33/0.97  --symbol_type_check                     false
% 1.33/0.97  --clausify_out                          false
% 1.33/0.97  --sig_cnt_out                           false
% 1.33/0.97  --trig_cnt_out                          false
% 1.33/0.97  --trig_cnt_out_tolerance                1.
% 1.33/0.97  --trig_cnt_out_sk_spl                   false
% 1.33/0.97  --abstr_cl_out                          false
% 1.33/0.97  
% 1.33/0.97  ------ Global Options
% 1.33/0.97  
% 1.33/0.97  --schedule                              default
% 1.33/0.97  --add_important_lit                     false
% 1.33/0.97  --prop_solver_per_cl                    1000
% 1.33/0.97  --min_unsat_core                        false
% 1.33/0.97  --soft_assumptions                      false
% 1.33/0.97  --soft_lemma_size                       3
% 1.33/0.97  --prop_impl_unit_size                   0
% 1.33/0.97  --prop_impl_unit                        []
% 1.33/0.97  --share_sel_clauses                     true
% 1.33/0.97  --reset_solvers                         false
% 1.33/0.97  --bc_imp_inh                            [conj_cone]
% 1.33/0.97  --conj_cone_tolerance                   3.
% 1.33/0.97  --extra_neg_conj                        none
% 1.33/0.97  --large_theory_mode                     true
% 1.33/0.97  --prolific_symb_bound                   200
% 1.33/0.97  --lt_threshold                          2000
% 1.33/0.97  --clause_weak_htbl                      true
% 1.33/0.97  --gc_record_bc_elim                     false
% 1.33/0.97  
% 1.33/0.97  ------ Preprocessing Options
% 1.33/0.97  
% 1.33/0.97  --preprocessing_flag                    true
% 1.33/0.97  --time_out_prep_mult                    0.1
% 1.33/0.97  --splitting_mode                        input
% 1.33/0.97  --splitting_grd                         true
% 1.33/0.97  --splitting_cvd                         false
% 1.33/0.97  --splitting_cvd_svl                     false
% 1.33/0.97  --splitting_nvd                         32
% 1.33/0.97  --sub_typing                            true
% 1.33/0.97  --prep_gs_sim                           true
% 1.33/0.97  --prep_unflatten                        true
% 1.33/0.97  --prep_res_sim                          true
% 1.33/0.97  --prep_upred                            true
% 1.33/0.97  --prep_sem_filter                       exhaustive
% 1.33/0.97  --prep_sem_filter_out                   false
% 1.33/0.98  --pred_elim                             true
% 1.33/0.98  --res_sim_input                         true
% 1.33/0.98  --eq_ax_congr_red                       true
% 1.33/0.98  --pure_diseq_elim                       true
% 1.33/0.98  --brand_transform                       false
% 1.33/0.98  --non_eq_to_eq                          false
% 1.33/0.98  --prep_def_merge                        true
% 1.33/0.98  --prep_def_merge_prop_impl              false
% 1.33/0.98  --prep_def_merge_mbd                    true
% 1.33/0.98  --prep_def_merge_tr_red                 false
% 1.33/0.98  --prep_def_merge_tr_cl                  false
% 1.33/0.98  --smt_preprocessing                     true
% 1.33/0.98  --smt_ac_axioms                         fast
% 1.33/0.98  --preprocessed_out                      false
% 1.33/0.98  --preprocessed_stats                    false
% 1.33/0.98  
% 1.33/0.98  ------ Abstraction refinement Options
% 1.33/0.98  
% 1.33/0.98  --abstr_ref                             []
% 1.33/0.98  --abstr_ref_prep                        false
% 1.33/0.98  --abstr_ref_until_sat                   false
% 1.33/0.98  --abstr_ref_sig_restrict                funpre
% 1.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/0.98  --abstr_ref_under                       []
% 1.33/0.98  
% 1.33/0.98  ------ SAT Options
% 1.33/0.98  
% 1.33/0.98  --sat_mode                              false
% 1.33/0.98  --sat_fm_restart_options                ""
% 1.33/0.98  --sat_gr_def                            false
% 1.33/0.98  --sat_epr_types                         true
% 1.33/0.98  --sat_non_cyclic_types                  false
% 1.33/0.98  --sat_finite_models                     false
% 1.33/0.98  --sat_fm_lemmas                         false
% 1.33/0.98  --sat_fm_prep                           false
% 1.33/0.98  --sat_fm_uc_incr                        true
% 1.33/0.98  --sat_out_model                         small
% 1.33/0.98  --sat_out_clauses                       false
% 1.33/0.98  
% 1.33/0.98  ------ QBF Options
% 1.33/0.98  
% 1.33/0.98  --qbf_mode                              false
% 1.33/0.98  --qbf_elim_univ                         false
% 1.33/0.98  --qbf_dom_inst                          none
% 1.33/0.98  --qbf_dom_pre_inst                      false
% 1.33/0.98  --qbf_sk_in                             false
% 1.33/0.98  --qbf_pred_elim                         true
% 1.33/0.98  --qbf_split                             512
% 1.33/0.98  
% 1.33/0.98  ------ BMC1 Options
% 1.33/0.98  
% 1.33/0.98  --bmc1_incremental                      false
% 1.33/0.98  --bmc1_axioms                           reachable_all
% 1.33/0.98  --bmc1_min_bound                        0
% 1.33/0.98  --bmc1_max_bound                        -1
% 1.33/0.98  --bmc1_max_bound_default                -1
% 1.33/0.98  --bmc1_symbol_reachability              true
% 1.33/0.98  --bmc1_property_lemmas                  false
% 1.33/0.98  --bmc1_k_induction                      false
% 1.33/0.98  --bmc1_non_equiv_states                 false
% 1.33/0.98  --bmc1_deadlock                         false
% 1.33/0.98  --bmc1_ucm                              false
% 1.33/0.98  --bmc1_add_unsat_core                   none
% 1.33/0.98  --bmc1_unsat_core_children              false
% 1.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/0.98  --bmc1_out_stat                         full
% 1.33/0.98  --bmc1_ground_init                      false
% 1.33/0.98  --bmc1_pre_inst_next_state              false
% 1.33/0.98  --bmc1_pre_inst_state                   false
% 1.33/0.98  --bmc1_pre_inst_reach_state             false
% 1.33/0.98  --bmc1_out_unsat_core                   false
% 1.33/0.98  --bmc1_aig_witness_out                  false
% 1.33/0.98  --bmc1_verbose                          false
% 1.33/0.98  --bmc1_dump_clauses_tptp                false
% 1.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.33/0.98  --bmc1_dump_file                        -
% 1.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.33/0.98  --bmc1_ucm_extend_mode                  1
% 1.33/0.98  --bmc1_ucm_init_mode                    2
% 1.33/0.98  --bmc1_ucm_cone_mode                    none
% 1.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.33/0.98  --bmc1_ucm_relax_model                  4
% 1.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/0.98  --bmc1_ucm_layered_model                none
% 1.33/0.98  --bmc1_ucm_max_lemma_size               10
% 1.33/0.98  
% 1.33/0.98  ------ AIG Options
% 1.33/0.98  
% 1.33/0.98  --aig_mode                              false
% 1.33/0.98  
% 1.33/0.98  ------ Instantiation Options
% 1.33/0.98  
% 1.33/0.98  --instantiation_flag                    true
% 1.33/0.98  --inst_sos_flag                         false
% 1.33/0.98  --inst_sos_phase                        true
% 1.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/0.98  --inst_lit_sel_side                     none
% 1.33/0.98  --inst_solver_per_active                1400
% 1.33/0.98  --inst_solver_calls_frac                1.
% 1.33/0.98  --inst_passive_queue_type               priority_queues
% 1.33/0.98  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.33/0.98  --inst_passive_queues_freq              [25;2]
% 1.33/0.98  --inst_dismatching                      true
% 1.33/0.98  --inst_eager_unprocessed_to_passive     true
% 1.33/0.98  --inst_prop_sim_given                   true
% 1.33/0.98  --inst_prop_sim_new                     false
% 1.33/0.98  --inst_subs_new                         false
% 1.33/0.98  --inst_eq_res_simp                      false
% 1.33/0.98  --inst_subs_given                       false
% 1.33/0.98  --inst_orphan_elimination               true
% 1.33/0.98  --inst_learning_loop_flag               true
% 1.33/0.98  --inst_learning_start                   3000
% 1.33/0.98  --inst_learning_factor                  2
% 1.33/0.98  --inst_start_prop_sim_after_learn       3
% 1.33/0.98  --inst_sel_renew                        solver
% 1.33/0.98  --inst_lit_activity_flag                true
% 1.33/0.98  --inst_restr_to_given                   false
% 1.33/0.98  --inst_activity_threshold               500
% 1.33/0.98  --inst_out_proof                        true
% 1.33/0.98  
% 1.33/0.98  ------ Resolution Options
% 1.33/0.98  
% 1.33/0.98  --resolution_flag                       false
% 1.33/0.98  --res_lit_sel                           adaptive
% 1.33/0.98  --res_lit_sel_side                      none
% 1.33/0.98  --res_ordering                          kbo
% 1.33/0.98  --res_to_prop_solver                    active
% 1.33/0.98  --res_prop_simpl_new                    false
% 1.33/0.98  --res_prop_simpl_given                  true
% 1.33/0.98  --res_passive_queue_type                priority_queues
% 1.33/0.98  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.33/0.98  --res_passive_queues_freq               [15;5]
% 1.33/0.98  --res_forward_subs                      full
% 1.33/0.98  --res_backward_subs                     full
% 1.33/0.98  --res_forward_subs_resolution           true
% 1.33/0.98  --res_backward_subs_resolution          true
% 1.33/0.98  --res_orphan_elimination                true
% 1.33/0.98  --res_time_limit                        2.
% 1.33/0.98  --res_out_proof                         true
% 1.33/0.98  
% 1.33/0.98  ------ Superposition Options
% 1.33/0.98  
% 1.33/0.98  --superposition_flag                    true
% 1.33/0.98  --sup_passive_queue_type                priority_queues
% 1.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.33/0.98  --demod_completeness_check              fast
% 1.33/0.98  --demod_use_ground                      true
% 1.33/0.98  --sup_to_prop_solver                    passive
% 1.33/0.98  --sup_prop_simpl_new                    true
% 1.33/0.98  --sup_prop_simpl_given                  true
% 1.33/0.98  --sup_fun_splitting                     false
% 1.33/0.98  --sup_smt_interval                      50000
% 1.33/0.98  
% 1.33/0.98  ------ Superposition Simplification Setup
% 1.33/0.98  
% 1.33/0.98  --sup_indices_passive                   []
% 1.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_full_bw                           [BwDemod]
% 1.33/0.98  --sup_immed_triv                        [TrivRules]
% 1.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_immed_bw_main                     []
% 1.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.98  
% 1.33/0.98  ------ Combination Options
% 1.33/0.98  
% 1.33/0.98  --comb_res_mult                         3
% 1.33/0.98  --comb_sup_mult                         2
% 1.33/0.98  --comb_inst_mult                        10
% 1.33/0.98  
% 1.33/0.98  ------ Debug Options
% 1.33/0.98  
% 1.33/0.98  --dbg_backtrace                         false
% 1.33/0.98  --dbg_dump_prop_clauses                 false
% 1.33/0.98  --dbg_dump_prop_clauses_file            -
% 1.33/0.98  --dbg_out_stat                          false
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  ------ Proving...
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  % SZS status Theorem for theBenchmark.p
% 1.33/0.98  
% 1.33/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.33/0.98  
% 1.33/0.98  fof(f8,axiom,(
% 1.33/0.98    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k2_yellow_0(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)))))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f27,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_yellow_0(X0,X2) = X1 <=> (! [X3] : ((r1_orders_2(X0,X3,X1) | ~r1_lattice3(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.33/0.98    inference(ennf_transformation,[],[f8])).
% 1.33/0.98  
% 1.33/0.98  fof(f28,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_yellow_0(X0,X2) = X1 <=> (! [X3] : (r1_orders_2(X0,X3,X1) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(flattening,[],[f27])).
% 1.33/0.98  
% 1.33/0.98  fof(f43,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_yellow_0(X0,X2) = X1 | (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X3] : (r1_orders_2(X0,X3,X1) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(nnf_transformation,[],[f28])).
% 1.33/0.98  
% 1.33/0.98  fof(f44,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_yellow_0(X0,X2) = X1 | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X3] : (r1_orders_2(X0,X3,X1) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(flattening,[],[f43])).
% 1.33/0.98  
% 1.33/0.98  fof(f45,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_yellow_0(X0,X2) = X1 | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(rectify,[],[f44])).
% 1.33/0.98  
% 1.33/0.98  fof(f46,plain,(
% 1.33/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 1.33/0.98    introduced(choice_axiom,[])).
% 1.33/0.98  
% 1.33/0.98  fof(f47,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_yellow_0(X0,X2) = X1 | (~r1_orders_2(X0,sK2(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 1.33/0.98  
% 1.33/0.98  fof(f68,plain,(
% 1.33/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f47])).
% 1.33/0.98  
% 1.33/0.98  fof(f85,plain,(
% 1.33/0.98    ( ! [X4,X2,X0] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X2)) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(equality_resolution,[],[f68])).
% 1.33/0.98  
% 1.33/0.98  fof(f5,axiom,(
% 1.33/0.98    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f22,plain,(
% 1.33/0.98    ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(ennf_transformation,[],[f5])).
% 1.33/0.98  
% 1.33/0.98  fof(f60,plain,(
% 1.33/0.98    ( ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f22])).
% 1.33/0.98  
% 1.33/0.98  fof(f2,axiom,(
% 1.33/0.98    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f17,plain,(
% 1.33/0.98    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(ennf_transformation,[],[f2])).
% 1.33/0.98  
% 1.33/0.98  fof(f18,plain,(
% 1.33/0.98    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(flattening,[],[f17])).
% 1.33/0.98  
% 1.33/0.98  fof(f53,plain,(
% 1.33/0.98    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f18])).
% 1.33/0.98  
% 1.33/0.98  fof(f10,conjecture,(
% 1.33/0.98    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f11,negated_conjecture,(
% 1.33/0.98    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.33/0.98    inference(negated_conjecture,[],[f10])).
% 1.33/0.98  
% 1.33/0.98  fof(f12,plain,(
% 1.33/0.98    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.33/0.98    inference(pure_predicate_removal,[],[f11])).
% 1.33/0.98  
% 1.33/0.98  fof(f13,plain,(
% 1.33/0.98    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.33/0.98    inference(pure_predicate_removal,[],[f12])).
% 1.33/0.98  
% 1.33/0.98  fof(f30,plain,(
% 1.33/0.98    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & (l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.33/0.98    inference(ennf_transformation,[],[f13])).
% 1.33/0.98  
% 1.33/0.98  fof(f31,plain,(
% 1.33/0.98    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.33/0.98    inference(flattening,[],[f30])).
% 1.33/0.98  
% 1.33/0.98  fof(f49,plain,(
% 1.33/0.98    ( ! [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) => ((~r1_orders_2(X0,k2_yellow_0(X0,sK5),k2_yellow_0(X0,sK4)) | ~r3_orders_2(X0,k1_yellow_0(X0,sK4),k1_yellow_0(X0,sK5))) & r1_tarski(sK4,sK5))) )),
% 1.33/0.98    introduced(choice_axiom,[])).
% 1.33/0.98  
% 1.33/0.98  fof(f48,plain,(
% 1.33/0.98    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X2,X1] : ((~r1_orders_2(sK3,k2_yellow_0(sK3,X2),k2_yellow_0(sK3,X1)) | ~r3_orders_2(sK3,k1_yellow_0(sK3,X1),k1_yellow_0(sK3,X2))) & r1_tarski(X1,X2)) & l1_orders_2(sK3) & v3_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v3_orders_2(sK3))),
% 1.33/0.98    introduced(choice_axiom,[])).
% 1.33/0.98  
% 1.33/0.98  fof(f50,plain,(
% 1.33/0.98    ((~r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4)) | ~r3_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5))) & r1_tarski(sK4,sK5)) & l1_orders_2(sK3) & v3_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v3_orders_2(sK3)),
% 1.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f31,f49,f48])).
% 1.33/0.98  
% 1.33/0.98  fof(f76,plain,(
% 1.33/0.98    v1_lattice3(sK3)),
% 1.33/0.98    inference(cnf_transformation,[],[f50])).
% 1.33/0.98  
% 1.33/0.98  fof(f78,plain,(
% 1.33/0.98    l1_orders_2(sK3)),
% 1.33/0.98    inference(cnf_transformation,[],[f50])).
% 1.33/0.98  
% 1.33/0.98  fof(f75,plain,(
% 1.33/0.98    v5_orders_2(sK3)),
% 1.33/0.98    inference(cnf_transformation,[],[f50])).
% 1.33/0.98  
% 1.33/0.98  fof(f77,plain,(
% 1.33/0.98    v3_lattice3(sK3)),
% 1.33/0.98    inference(cnf_transformation,[],[f50])).
% 1.33/0.98  
% 1.33/0.98  fof(f7,axiom,(
% 1.33/0.98    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k1_yellow_0(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)))))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f25,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : (k1_yellow_0(X0,X2) = X1 <=> (! [X3] : ((r1_orders_2(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.33/0.98    inference(ennf_transformation,[],[f7])).
% 1.33/0.98  
% 1.33/0.98  fof(f26,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : (k1_yellow_0(X0,X2) = X1 <=> (! [X3] : (r1_orders_2(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(flattening,[],[f25])).
% 1.33/0.98  
% 1.33/0.98  fof(f38,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_yellow_0(X0,X2) = X1 | (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X3] : (r1_orders_2(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(nnf_transformation,[],[f26])).
% 1.33/0.98  
% 1.33/0.98  fof(f39,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_yellow_0(X0,X2) = X1 | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X3] : (r1_orders_2(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(flattening,[],[f38])).
% 1.33/0.98  
% 1.33/0.98  fof(f40,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_yellow_0(X0,X2) = X1 | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(rectify,[],[f39])).
% 1.33/0.98  
% 1.33/0.98  fof(f41,plain,(
% 1.33/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.33/0.98    introduced(choice_axiom,[])).
% 1.33/0.98  
% 1.33/0.98  fof(f42,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_yellow_0(X0,X2) = X1 | (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 1.33/0.98  
% 1.33/0.98  fof(f63,plain,(
% 1.33/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f42])).
% 1.33/0.98  
% 1.33/0.98  fof(f83,plain,(
% 1.33/0.98    ( ! [X4,X2,X0] : (r1_orders_2(X0,k1_yellow_0(X0,X2),X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(equality_resolution,[],[f63])).
% 1.33/0.98  
% 1.33/0.98  fof(f4,axiom,(
% 1.33/0.98    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f21,plain,(
% 1.33/0.98    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(ennf_transformation,[],[f4])).
% 1.33/0.98  
% 1.33/0.98  fof(f59,plain,(
% 1.33/0.98    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f21])).
% 1.33/0.98  
% 1.33/0.98  fof(f62,plain,(
% 1.33/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X2,X1) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f42])).
% 1.33/0.98  
% 1.33/0.98  fof(f84,plain,(
% 1.33/0.98    ( ! [X2,X0] : (r2_lattice3(X0,X2,k1_yellow_0(X0,X2)) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(equality_resolution,[],[f62])).
% 1.33/0.98  
% 1.33/0.98  fof(f9,axiom,(
% 1.33/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f29,plain,(
% 1.33/0.98    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(ennf_transformation,[],[f9])).
% 1.33/0.98  
% 1.33/0.98  fof(f73,plain,(
% 1.33/0.98    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f29])).
% 1.33/0.98  
% 1.33/0.98  fof(f79,plain,(
% 1.33/0.98    r1_tarski(sK4,sK5)),
% 1.33/0.98    inference(cnf_transformation,[],[f50])).
% 1.33/0.98  
% 1.33/0.98  fof(f67,plain,(
% 1.33/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X2,X1) | k2_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f47])).
% 1.33/0.98  
% 1.33/0.98  fof(f86,plain,(
% 1.33/0.98    ( ! [X2,X0] : (r1_lattice3(X0,X2,k2_yellow_0(X0,X2)) | ~m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(equality_resolution,[],[f67])).
% 1.33/0.98  
% 1.33/0.98  fof(f6,axiom,(
% 1.33/0.98    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f14,plain,(
% 1.33/0.98    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : r2_yellow_0(X0,X1))),
% 1.33/0.98    inference(pure_predicate_removal,[],[f6])).
% 1.33/0.98  
% 1.33/0.98  fof(f23,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : r2_yellow_0(X0,X1) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.33/0.98    inference(ennf_transformation,[],[f14])).
% 1.33/0.98  
% 1.33/0.98  fof(f24,plain,(
% 1.33/0.98    ! [X0] : (! [X1] : r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(flattening,[],[f23])).
% 1.33/0.98  
% 1.33/0.98  fof(f61,plain,(
% 1.33/0.98    ( ! [X0,X1] : (r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f24])).
% 1.33/0.98  
% 1.33/0.98  fof(f3,axiom,(
% 1.33/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f19,plain,(
% 1.33/0.98    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(ennf_transformation,[],[f3])).
% 1.33/0.98  
% 1.33/0.98  fof(f20,plain,(
% 1.33/0.98    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(flattening,[],[f19])).
% 1.33/0.98  
% 1.33/0.98  fof(f33,plain,(
% 1.33/0.98    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(nnf_transformation,[],[f20])).
% 1.33/0.98  
% 1.33/0.98  fof(f34,plain,(
% 1.33/0.98    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(flattening,[],[f33])).
% 1.33/0.98  
% 1.33/0.98  fof(f35,plain,(
% 1.33/0.98    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(rectify,[],[f34])).
% 1.33/0.98  
% 1.33/0.98  fof(f36,plain,(
% 1.33/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.33/0.98    introduced(choice_axiom,[])).
% 1.33/0.98  
% 1.33/0.98  fof(f37,plain,(
% 1.33/0.98    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 1.33/0.98  
% 1.33/0.98  fof(f54,plain,(
% 1.33/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f37])).
% 1.33/0.98  
% 1.33/0.98  fof(f82,plain,(
% 1.33/0.98    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.98    inference(equality_resolution,[],[f54])).
% 1.33/0.98  
% 1.33/0.98  fof(f72,plain,(
% 1.33/0.98    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f29])).
% 1.33/0.98  
% 1.33/0.98  fof(f80,plain,(
% 1.33/0.98    ~r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4)) | ~r3_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5))),
% 1.33/0.98    inference(cnf_transformation,[],[f50])).
% 1.33/0.98  
% 1.33/0.98  fof(f1,axiom,(
% 1.33/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.98  
% 1.33/0.98  fof(f15,plain,(
% 1.33/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.33/0.98    inference(ennf_transformation,[],[f1])).
% 1.33/0.98  
% 1.33/0.98  fof(f16,plain,(
% 1.33/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(flattening,[],[f15])).
% 1.33/0.98  
% 1.33/0.98  fof(f32,plain,(
% 1.33/0.98    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.98    inference(nnf_transformation,[],[f16])).
% 1.33/0.98  
% 1.33/0.98  fof(f52,plain,(
% 1.33/0.98    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.98    inference(cnf_transformation,[],[f32])).
% 1.33/0.98  
% 1.33/0.98  fof(f74,plain,(
% 1.33/0.98    v3_orders_2(sK3)),
% 1.33/0.98    inference(cnf_transformation,[],[f50])).
% 1.33/0.98  
% 1.33/0.98  cnf(c_19,plain,
% 1.33/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.33/0.98      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f85]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_9,plain,
% 1.33/0.98      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_179,plain,
% 1.33/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.33/0.98      | ~ r1_lattice3(X0,X1,X2)
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_19,c_9]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_180,plain,
% 1.33/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.33/0.98      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_179]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_2,plain,
% 1.33/0.98      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_27,negated_conjecture,
% 1.33/0.98      ( v1_lattice3(sK3) ),
% 1.33/0.98      inference(cnf_transformation,[],[f76]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_367,plain,
% 1.33/0.98      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_27]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_368,plain,
% 1.33/0.98      ( ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_367]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_25,negated_conjecture,
% 1.33/0.98      ( l1_orders_2(sK3) ),
% 1.33/0.98      inference(cnf_transformation,[],[f78]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_94,plain,
% 1.33/0.98      ( ~ v1_lattice3(sK3) | ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_370,plain,
% 1.33/0.98      ( ~ v2_struct_0(sK3) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_368,c_27,c_25,c_94]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_730,plain,
% 1.33/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.33/0.98      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | ~ l1_orders_2(X0)
% 1.33/0.98      | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_180,c_370]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_731,plain,
% 1.33/0.98      ( ~ r1_lattice3(sK3,X0,X1)
% 1.33/0.98      | r1_orders_2(sK3,X1,k2_yellow_0(sK3,X0))
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.33/0.98      | ~ v5_orders_2(sK3)
% 1.33/0.98      | ~ v3_lattice3(sK3)
% 1.33/0.98      | ~ l1_orders_2(sK3) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_730]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_28,negated_conjecture,
% 1.33/0.98      ( v5_orders_2(sK3) ),
% 1.33/0.98      inference(cnf_transformation,[],[f75]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_26,negated_conjecture,
% 1.33/0.98      ( v3_lattice3(sK3) ),
% 1.33/0.98      inference(cnf_transformation,[],[f77]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_735,plain,
% 1.33/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.33/0.98      | r1_orders_2(sK3,X1,k2_yellow_0(sK3,X0))
% 1.33/0.98      | ~ r1_lattice3(sK3,X0,X1) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_731,c_28,c_26,c_25]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_736,plain,
% 1.33/0.98      ( ~ r1_lattice3(sK3,X0,X1)
% 1.33/0.98      | r1_orders_2(sK3,X1,k2_yellow_0(sK3,X0))
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_735]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1162,plain,
% 1.33/0.98      ( ~ r1_lattice3(sK3,X0_52,X0_51)
% 1.33/0.98      | r1_orders_2(sK3,X0_51,k2_yellow_0(sK3,X0_52))
% 1.33/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(subtyping,[status(esa)],[c_736]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1707,plain,
% 1.33/0.98      ( ~ r1_lattice3(sK3,X0_52,k2_yellow_0(sK3,X1_52))
% 1.33/0.98      | r1_orders_2(sK3,k2_yellow_0(sK3,X1_52),k2_yellow_0(sK3,X0_52))
% 1.33/0.98      | ~ m1_subset_1(k2_yellow_0(sK3,X1_52),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1162]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_2002,plain,
% 1.33/0.98      ( ~ r1_lattice3(sK3,sK4,k2_yellow_0(sK3,sK5))
% 1.33/0.98      | r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
% 1.33/0.98      | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1707]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_14,plain,
% 1.33/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 1.33/0.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f83]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_8,plain,
% 1.33/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_196,plain,
% 1.33/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.33/0.98      | ~ r2_lattice3(X0,X1,X2)
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_14,c_8]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_197,plain,
% 1.33/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 1.33/0.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_196]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_694,plain,
% 1.33/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 1.33/0.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | ~ l1_orders_2(X0)
% 1.33/0.98      | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_197,c_370]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_695,plain,
% 1.33/0.98      ( ~ r2_lattice3(sK3,X0,X1)
% 1.33/0.98      | r1_orders_2(sK3,k1_yellow_0(sK3,X0),X1)
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.33/0.98      | ~ v5_orders_2(sK3)
% 1.33/0.98      | ~ v3_lattice3(sK3)
% 1.33/0.98      | ~ l1_orders_2(sK3) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_694]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_699,plain,
% 1.33/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.33/0.98      | r1_orders_2(sK3,k1_yellow_0(sK3,X0),X1)
% 1.33/0.98      | ~ r2_lattice3(sK3,X0,X1) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_695,c_28,c_26,c_25]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_700,plain,
% 1.33/0.98      ( ~ r2_lattice3(sK3,X0,X1)
% 1.33/0.98      | r1_orders_2(sK3,k1_yellow_0(sK3,X0),X1)
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_699]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1164,plain,
% 1.33/0.98      ( ~ r2_lattice3(sK3,X0_52,X0_51)
% 1.33/0.98      | r1_orders_2(sK3,k1_yellow_0(sK3,X0_52),X0_51)
% 1.33/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(subtyping,[status(esa)],[c_700]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1712,plain,
% 1.33/0.98      ( ~ r2_lattice3(sK3,X0_52,k1_yellow_0(sK3,X1_52))
% 1.33/0.98      | r1_orders_2(sK3,k1_yellow_0(sK3,X0_52),k1_yellow_0(sK3,X1_52))
% 1.33/0.98      | ~ m1_subset_1(k1_yellow_0(sK3,X1_52),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1164]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1922,plain,
% 1.33/0.98      ( ~ r2_lattice3(sK3,sK4,k1_yellow_0(sK3,sK5))
% 1.33/0.98      | r1_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5))
% 1.33/0.98      | ~ m1_subset_1(k1_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1712]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_997,plain,
% 1.33/0.98      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_998,plain,
% 1.33/0.98      ( m1_subset_1(k2_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_997]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1152,plain,
% 1.33/0.98      ( m1_subset_1(k2_yellow_0(sK3,X0_52),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(subtyping,[status(esa)],[c_998]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1890,plain,
% 1.33/0.98      ( m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1152]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_15,plain,
% 1.33/0.98      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.33/0.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f84]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_189,plain,
% 1.33/0.98      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_15,c_8]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_715,plain,
% 1.33/0.98      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | ~ l1_orders_2(X0)
% 1.33/0.98      | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_189,c_370]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_716,plain,
% 1.33/0.98      ( r2_lattice3(sK3,X0,k1_yellow_0(sK3,X0))
% 1.33/0.98      | ~ v5_orders_2(sK3)
% 1.33/0.98      | ~ v3_lattice3(sK3)
% 1.33/0.98      | ~ l1_orders_2(sK3) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_715]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_720,plain,
% 1.33/0.98      ( r2_lattice3(sK3,X0,k1_yellow_0(sK3,X0)) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_716,c_28,c_26,c_25]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1163,plain,
% 1.33/0.98      ( r2_lattice3(sK3,X0_52,k1_yellow_0(sK3,X0_52)) ),
% 1.33/0.98      inference(subtyping,[status(esa)],[c_720]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1697,plain,
% 1.33/0.98      ( r2_lattice3(sK3,sK5,k1_yellow_0(sK3,sK5)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1163]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_21,plain,
% 1.33/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 1.33/0.98      | r2_lattice3(X0,X3,X2)
% 1.33/0.98      | ~ r1_tarski(X3,X1)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_24,negated_conjecture,
% 1.33/0.98      ( r1_tarski(sK4,sK5) ),
% 1.33/0.98      inference(cnf_transformation,[],[f79]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_398,plain,
% 1.33/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 1.33/0.98      | r2_lattice3(X0,X3,X2)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0)
% 1.33/0.98      | sK4 != X3
% 1.33/0.98      | sK5 != X1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_399,plain,
% 1.33/0.98      ( r2_lattice3(X0,sK4,X1)
% 1.33/0.98      | ~ r2_lattice3(X0,sK5,X1)
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_398]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_967,plain,
% 1.33/0.98      ( r2_lattice3(X0,sK4,X1)
% 1.33/0.98      | ~ r2_lattice3(X0,sK5,X1)
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/0.98      | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_399,c_25]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_968,plain,
% 1.33/0.98      ( r2_lattice3(sK3,sK4,X0)
% 1.33/0.98      | ~ r2_lattice3(sK3,sK5,X0)
% 1.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_967]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1154,plain,
% 1.33/0.98      ( r2_lattice3(sK3,sK4,X0_51)
% 1.33/0.98      | ~ r2_lattice3(sK3,sK5,X0_51)
% 1.33/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(subtyping,[status(esa)],[c_968]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1696,plain,
% 1.33/0.98      ( r2_lattice3(sK3,sK4,k1_yellow_0(sK3,sK5))
% 1.33/0.98      | ~ r2_lattice3(sK3,sK5,k1_yellow_0(sK3,sK5))
% 1.33/0.98      | ~ m1_subset_1(k1_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1154]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_20,plain,
% 1.33/0.98      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.33/0.98      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f86]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_10,plain,
% 1.33/0.98      ( r2_yellow_0(X0,X1)
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_7,plain,
% 1.33/0.98      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.33/0.98      | ~ r2_yellow_0(X0,X1)
% 1.33/0.98      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f82]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_172,plain,
% 1.33/0.98      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_20,c_10,c_9,c_7]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_751,plain,
% 1.33/0.98      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.33/0.98      | ~ v5_orders_2(X0)
% 1.33/0.98      | ~ v3_lattice3(X0)
% 1.33/0.98      | ~ l1_orders_2(X0)
% 1.33/0.98      | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_172,c_370]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_752,plain,
% 1.33/0.98      ( r1_lattice3(sK3,X0,k2_yellow_0(sK3,X0))
% 1.33/0.98      | ~ v5_orders_2(sK3)
% 1.33/0.98      | ~ v3_lattice3(sK3)
% 1.33/0.98      | ~ l1_orders_2(sK3) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_751]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_756,plain,
% 1.33/0.98      ( r1_lattice3(sK3,X0,k2_yellow_0(sK3,X0)) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_752,c_28,c_26,c_25]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1161,plain,
% 1.33/0.98      ( r1_lattice3(sK3,X0_52,k2_yellow_0(sK3,X0_52)) ),
% 1.33/0.98      inference(subtyping,[status(esa)],[c_756]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1691,plain,
% 1.33/0.98      ( r1_lattice3(sK3,sK5,k2_yellow_0(sK3,sK5)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1161]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_22,plain,
% 1.33/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.33/0.98      | r1_lattice3(X0,X3,X2)
% 1.33/0.98      | ~ r1_tarski(X3,X1)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_380,plain,
% 1.33/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.33/0.98      | r1_lattice3(X0,X3,X2)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0)
% 1.33/0.98      | sK4 != X3
% 1.33/0.98      | sK5 != X1 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_24]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_381,plain,
% 1.33/0.98      ( r1_lattice3(X0,sK4,X1)
% 1.33/0.98      | ~ r1_lattice3(X0,sK5,X1)
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_380]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_982,plain,
% 1.33/0.98      ( r1_lattice3(X0,sK4,X1)
% 1.33/0.98      | ~ r1_lattice3(X0,sK5,X1)
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/0.98      | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_381,c_25]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_983,plain,
% 1.33/0.98      ( r1_lattice3(sK3,sK4,X0)
% 1.33/0.98      | ~ r1_lattice3(sK3,sK5,X0)
% 1.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_982]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1153,plain,
% 1.33/0.98      ( r1_lattice3(sK3,sK4,X0_51)
% 1.33/0.98      | ~ r1_lattice3(sK3,sK5,X0_51)
% 1.33/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(subtyping,[status(esa)],[c_983]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1690,plain,
% 1.33/0.98      ( r1_lattice3(sK3,sK4,k2_yellow_0(sK3,sK5))
% 1.33/0.98      | ~ r1_lattice3(sK3,sK5,k2_yellow_0(sK3,sK5))
% 1.33/0.98      | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1153]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1006,plain,
% 1.33/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1007,plain,
% 1.33/0.98      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_1006]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1151,plain,
% 1.33/0.98      ( m1_subset_1(k1_yellow_0(sK3,X0_52),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(subtyping,[status(esa)],[c_1007]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1687,plain,
% 1.33/0.98      ( m1_subset_1(k1_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1151]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_1230,plain,
% 1.33/0.98      ( m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(instantiation,[status(thm)],[c_1151]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_23,negated_conjecture,
% 1.33/0.98      ( ~ r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
% 1.33/0.98      | ~ r3_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5)) ),
% 1.33/0.98      inference(cnf_transformation,[],[f80]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_0,plain,
% 1.33/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 1.33/0.98      | r3_orders_2(X0,X1,X2)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ v3_orders_2(X0)
% 1.33/0.98      | ~ l1_orders_2(X0) ),
% 1.33/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_29,negated_conjecture,
% 1.33/0.98      ( v3_orders_2(sK3) ),
% 1.33/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_450,plain,
% 1.33/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 1.33/0.98      | r3_orders_2(X0,X1,X2)
% 1.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/0.98      | v2_struct_0(X0)
% 1.33/0.98      | ~ l1_orders_2(X0)
% 1.33/0.98      | sK3 != X0 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_29]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_451,plain,
% 1.33/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 1.33/0.98      | r3_orders_2(sK3,X0,X1)
% 1.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.33/0.98      | v2_struct_0(sK3)
% 1.33/0.98      | ~ l1_orders_2(sK3) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_450]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_455,plain,
% 1.33/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 1.33/0.98      | r3_orders_2(sK3,X0,X1)
% 1.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(global_propositional_subsumption,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_451,c_27,c_25,c_94]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_456,plain,
% 1.33/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 1.33/0.98      | r3_orders_2(sK3,X0,X1)
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.33/0.98      inference(renaming,[status(thm)],[c_455]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_485,plain,
% 1.33/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 1.33/0.98      | ~ r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
% 1.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.33/0.98      | k1_yellow_0(sK3,sK4) != X0
% 1.33/0.98      | k1_yellow_0(sK3,sK5) != X1
% 1.33/0.98      | sK3 != sK3 ),
% 1.33/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_456]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(c_486,plain,
% 1.33/0.98      ( ~ r1_orders_2(sK3,k1_yellow_0(sK3,sK4),k1_yellow_0(sK3,sK5))
% 1.33/0.98      | ~ r1_orders_2(sK3,k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4))
% 1.33/0.98      | ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK3))
% 1.33/0.98      | ~ m1_subset_1(k1_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
% 1.33/0.98      inference(unflattening,[status(thm)],[c_485]) ).
% 1.33/0.98  
% 1.33/0.98  cnf(contradiction,plain,
% 1.33/0.98      ( $false ),
% 1.33/0.98      inference(minisat,
% 1.33/0.98                [status(thm)],
% 1.33/0.98                [c_2002,c_1922,c_1890,c_1697,c_1696,c_1691,c_1690,c_1687,
% 1.33/0.98                 c_1230,c_486]) ).
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.33/0.98  
% 1.33/0.98  ------                               Statistics
% 1.33/0.98  
% 1.33/0.98  ------ General
% 1.33/0.98  
% 1.33/0.98  abstr_ref_over_cycles:                  0
% 1.33/0.98  abstr_ref_under_cycles:                 0
% 1.33/0.98  gc_basic_clause_elim:                   0
% 1.33/0.98  forced_gc_time:                         0
% 1.33/0.98  parsing_time:                           0.013
% 1.33/0.98  unif_index_cands_time:                  0.
% 1.33/0.98  unif_index_add_time:                    0.
% 1.33/0.98  orderings_time:                         0.
% 1.33/0.98  out_proof_time:                         0.015
% 1.33/0.98  total_time:                             0.101
% 1.33/0.98  num_of_symbols:                         54
% 1.33/0.98  num_of_terms:                           1499
% 1.33/0.98  
% 1.33/0.98  ------ Preprocessing
% 1.33/0.98  
% 1.33/0.98  num_of_splits:                          0
% 1.33/0.98  num_of_split_atoms:                     0
% 1.33/0.98  num_of_reused_defs:                     0
% 1.33/0.98  num_eq_ax_congr_red:                    43
% 1.33/0.98  num_of_sem_filtered_clauses:            1
% 1.33/0.98  num_of_subtypes:                        4
% 1.33/0.98  monotx_restored_types:                  0
% 1.33/0.98  sat_num_of_epr_types:                   0
% 1.33/0.98  sat_num_of_non_cyclic_types:            0
% 1.33/0.98  sat_guarded_non_collapsed_types:        1
% 1.33/0.98  num_pure_diseq_elim:                    0
% 1.33/0.98  simp_replaced_by:                       0
% 1.33/0.98  res_preprocessed:                       97
% 1.33/0.98  prep_upred:                             0
% 1.33/0.98  prep_unflattend:                        26
% 1.33/0.98  smt_new_axioms:                         0
% 1.33/0.98  pred_elim_cands:                        4
% 1.33/0.98  pred_elim:                              9
% 1.33/0.98  pred_elim_cl:                           12
% 1.33/0.98  pred_elim_cycles:                       11
% 1.33/0.98  merged_defs:                            0
% 1.33/0.98  merged_defs_ncl:                        0
% 1.33/0.98  bin_hyper_res:                          0
% 1.33/0.98  prep_cycles:                            4
% 1.33/0.98  pred_elim_time:                         0.014
% 1.33/0.98  splitting_time:                         0.
% 1.33/0.98  sem_filter_time:                        0.
% 1.33/0.98  monotx_time:                            0.
% 1.33/0.98  subtype_inf_time:                       0.
% 1.33/0.98  
% 1.33/0.98  ------ Problem properties
% 1.33/0.98  
% 1.33/0.98  clauses:                                18
% 1.33/0.98  conjectures:                            0
% 1.33/0.98  epr:                                    0
% 1.33/0.98  horn:                                   12
% 1.33/0.98  ground:                                 1
% 1.33/0.98  unary:                                  4
% 1.33/0.98  binary:                                 0
% 1.33/0.98  lits:                                   55
% 1.33/0.98  lits_eq:                                9
% 1.33/0.98  fd_pure:                                0
% 1.33/0.98  fd_pseudo:                              0
% 1.33/0.98  fd_cond:                                0
% 1.33/0.98  fd_pseudo_cond:                         9
% 1.33/0.98  ac_symbols:                             0
% 1.33/0.98  
% 1.33/0.98  ------ Propositional Solver
% 1.33/0.98  
% 1.33/0.98  prop_solver_calls:                      24
% 1.33/0.98  prop_fast_solver_calls:                 936
% 1.33/0.98  smt_solver_calls:                       0
% 1.33/0.98  smt_fast_solver_calls:                  0
% 1.33/0.98  prop_num_of_clauses:                    535
% 1.33/0.98  prop_preprocess_simplified:             3121
% 1.33/0.98  prop_fo_subsumed:                       50
% 1.33/0.98  prop_solver_time:                       0.
% 1.33/0.98  smt_solver_time:                        0.
% 1.33/0.98  smt_fast_solver_time:                   0.
% 1.33/0.98  prop_fast_solver_time:                  0.
% 1.33/0.98  prop_unsat_core_time:                   0.
% 1.33/0.98  
% 1.33/0.98  ------ QBF
% 1.33/0.98  
% 1.33/0.98  qbf_q_res:                              0
% 1.33/0.98  qbf_num_tautologies:                    0
% 1.33/0.98  qbf_prep_cycles:                        0
% 1.33/0.98  
% 1.33/0.98  ------ BMC1
% 1.33/0.98  
% 1.33/0.98  bmc1_current_bound:                     -1
% 1.33/0.98  bmc1_last_solved_bound:                 -1
% 1.33/0.98  bmc1_unsat_core_size:                   -1
% 1.33/0.98  bmc1_unsat_core_parents_size:           -1
% 1.33/0.98  bmc1_merge_next_fun:                    0
% 1.33/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.33/0.98  
% 1.33/0.98  ------ Instantiation
% 1.33/0.98  
% 1.33/0.98  inst_num_of_clauses:                    70
% 1.33/0.98  inst_num_in_passive:                    10
% 1.33/0.98  inst_num_in_active:                     54
% 1.33/0.98  inst_num_in_unprocessed:                5
% 1.33/0.98  inst_num_of_loops:                      59
% 1.33/0.98  inst_num_of_learning_restarts:          0
% 1.33/0.98  inst_num_moves_active_passive:          3
% 1.33/0.98  inst_lit_activity:                      0
% 1.33/0.98  inst_lit_activity_moves:                0
% 1.33/0.98  inst_num_tautologies:                   0
% 1.33/0.98  inst_num_prop_implied:                  0
% 1.33/0.98  inst_num_existing_simplified:           0
% 1.33/0.98  inst_num_eq_res_simplified:             0
% 1.33/0.98  inst_num_child_elim:                    0
% 1.33/0.98  inst_num_of_dismatching_blockings:      26
% 1.33/0.98  inst_num_of_non_proper_insts:           57
% 1.33/0.98  inst_num_of_duplicates:                 0
% 1.33/0.98  inst_inst_num_from_inst_to_res:         0
% 1.33/0.98  inst_dismatching_checking_time:         0.
% 1.33/0.98  
% 1.33/0.98  ------ Resolution
% 1.33/0.98  
% 1.33/0.98  res_num_of_clauses:                     0
% 1.33/0.98  res_num_in_passive:                     0
% 1.33/0.98  res_num_in_active:                      0
% 1.33/0.98  res_num_of_loops:                       101
% 1.33/0.98  res_forward_subset_subsumed:            4
% 1.33/0.98  res_backward_subset_subsumed:           0
% 1.33/0.98  res_forward_subsumed:                   0
% 1.33/0.98  res_backward_subsumed:                  0
% 1.33/0.98  res_forward_subsumption_resolution:     0
% 1.33/0.98  res_backward_subsumption_resolution:    1
% 1.33/0.98  res_clause_to_clause_subsumption:       63
% 1.33/0.98  res_orphan_elimination:                 0
% 1.33/0.98  res_tautology_del:                      3
% 1.33/0.98  res_num_eq_res_simplified:              0
% 1.33/0.98  res_num_sel_changes:                    0
% 1.33/0.98  res_moves_from_active_to_pass:          0
% 1.33/0.98  
% 1.33/0.98  ------ Superposition
% 1.33/0.98  
% 1.33/0.98  sup_time_total:                         0.
% 1.33/0.98  sup_time_generating:                    0.
% 1.33/0.98  sup_time_sim_full:                      0.
% 1.33/0.98  sup_time_sim_immed:                     0.
% 1.33/0.98  
% 1.33/0.98  sup_num_of_clauses:                     23
% 1.33/0.98  sup_num_in_active:                      10
% 1.33/0.98  sup_num_in_passive:                     13
% 1.33/0.98  sup_num_of_loops:                       10
% 1.33/0.98  sup_fw_superposition:                   5
% 1.33/0.98  sup_bw_superposition:                   0
% 1.33/0.98  sup_immediate_simplified:               0
% 1.33/0.98  sup_given_eliminated:                   0
% 1.33/0.98  comparisons_done:                       0
% 1.33/0.98  comparisons_avoided:                    0
% 1.33/0.98  
% 1.33/0.98  ------ Simplifications
% 1.33/0.98  
% 1.33/0.98  
% 1.33/0.98  sim_fw_subset_subsumed:                 0
% 1.33/0.98  sim_bw_subset_subsumed:                 0
% 1.33/0.98  sim_fw_subsumed:                        0
% 1.33/0.98  sim_bw_subsumed:                        0
% 1.33/0.98  sim_fw_subsumption_res:                 1
% 1.33/0.98  sim_bw_subsumption_res:                 0
% 1.33/0.98  sim_tautology_del:                      0
% 1.33/0.98  sim_eq_tautology_del:                   0
% 1.33/0.98  sim_eq_res_simp:                        0
% 1.33/0.98  sim_fw_demodulated:                     0
% 1.33/0.98  sim_bw_demodulated:                     0
% 1.33/0.98  sim_light_normalised:                   0
% 1.33/0.98  sim_joinable_taut:                      0
% 1.33/0.98  sim_joinable_simp:                      0
% 1.33/0.98  sim_ac_normalised:                      0
% 1.33/0.98  sim_smt_subsumption:                    0
% 1.33/0.98  
%------------------------------------------------------------------------------
