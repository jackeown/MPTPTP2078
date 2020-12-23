%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1999+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:01 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  286 (68987 expanded)
%              Number of clauses        :  200 (8649 expanded)
%              Number of leaves         :   23 (23183 expanded)
%              Depth                    :   39
%              Number of atoms          : 1656 (1124517 expanded)
%              Number of equality atoms :  351 (3549 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   44 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v5_waybel_7(k1_waybel_4(X0),X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v5_waybel_7(k1_waybel_4(X0),X0)
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ( v4_waybel_7(X1,X0)
              <=> ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ~ r3_orders_2(X0,X3,X1)
                            & ~ r3_orders_2(X0,X2,X1)
                            & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_waybel_7(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_waybel_7(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X3,X1)
                    & ~ r3_orders_2(X0,X2,X1)
                    & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v4_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v4_waybel_7(X1,X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X3,X1)
                    & ~ r3_orders_2(X0,X2,X1)
                    & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v4_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v4_waybel_7(X1,X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X3,X1)
                    & ~ r3_orders_2(X0,X2,X1)
                    & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v4_waybel_7(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r3_orders_2(X0,X5,X1)
                    | r3_orders_2(X0,X4,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v4_waybel_7(X1,X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f48])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,X2,X1)
          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK7,X1)
        & ~ r3_orders_2(X0,X2,X1)
        & r1_waybel_3(X0,k12_lattice3(X0,X2,sK7),X1)
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_orders_2(X0,X3,X1)
              & ~ r3_orders_2(X0,X2,X1)
              & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r3_orders_2(X0,X3,X1)
            & ~ r3_orders_2(X0,sK6,X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK6,X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X3,X1)
                    & ~ r3_orders_2(X0,X2,X1)
                    & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v4_waybel_7(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r3_orders_2(X0,X5,X1)
                    | r3_orders_2(X0,X4,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v4_waybel_7(X1,X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,sK5)
                  & ~ r3_orders_2(X0,X2,sK5)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),sK5)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v4_waybel_7(sK5,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r3_orders_2(X0,X5,sK5)
                  | r3_orders_2(X0,X4,sK5)
                  | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),sK5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v4_waybel_7(sK5,X0) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X3,X1)
                      & ~ r3_orders_2(X0,X2,X1)
                      & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X5,X1)
                      | r3_orders_2(X0,X4,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v4_waybel_7(X1,X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & v5_waybel_7(k1_waybel_4(X0),X0)
        & l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(sK4,X3,X1)
                    & ~ r3_orders_2(sK4,X2,X1)
                    & r1_waybel_3(sK4,k12_lattice3(sK4,X2,X3),X1)
                    & m1_subset_1(X3,u1_struct_0(sK4)) )
                & m1_subset_1(X2,u1_struct_0(sK4)) )
            | ~ v4_waybel_7(X1,sK4) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r3_orders_2(sK4,X5,X1)
                    | r3_orders_2(sK4,X4,X1)
                    | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),X1)
                    | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
                | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
            | v4_waybel_7(X1,sK4) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & v5_waybel_7(k1_waybel_4(sK4),sK4)
      & l1_orders_2(sK4)
      & v3_waybel_3(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v1_yellow_0(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ( ~ r3_orders_2(sK4,sK7,sK5)
        & ~ r3_orders_2(sK4,sK6,sK5)
        & r1_waybel_3(sK4,k12_lattice3(sK4,sK6,sK7),sK5)
        & m1_subset_1(sK7,u1_struct_0(sK4))
        & m1_subset_1(sK6,u1_struct_0(sK4)) )
      | ~ v4_waybel_7(sK5,sK4) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r3_orders_2(sK4,X5,sK5)
              | r3_orders_2(sK4,X4,sK5)
              | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),sK5)
              | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
          | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
      | v4_waybel_7(sK5,sK4) )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & v5_waybel_7(k1_waybel_4(sK4),sK4)
    & l1_orders_2(sK4)
    & v3_waybel_3(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v1_yellow_0(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f49,f53,f52,f51,f50])).

fof(f91,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( ~ v5_waybel_6(X1,X0)
              & ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) )
              & v5_waybel_7(k1_waybel_4(X0),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,X2,X1)
          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK2(X0,X1),X1)
        & ~ r3_orders_2(X0,X2,X1)
        & r1_waybel_3(X0,k12_lattice3(X0,X2,sK2(X0,X1)),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_orders_2(X0,X3,X1)
              & ~ r3_orders_2(X0,X2,X1)
              & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r3_orders_2(X0,X3,X1)
            & ~ r3_orders_2(X0,sK1(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK1(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ( ~ r3_orders_2(X0,sK2(X0,X1),X1)
            & ~ r3_orders_2(X0,sK1(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK1(X0,X1),sK2(X0,X1)),X1)
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f43,f42])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | ~ r3_orders_2(X0,sK2(X0,X1),X1)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    v5_waybel_7(k1_waybel_4(sK4),sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    v3_waybel_3(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_waybel_7(X1,X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_waybel_7(X1,X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v4_waybel_7(X1,X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | ~ r3_orders_2(X0,sK1(X0,X1),X1)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X4,X5] :
      ( r3_orders_2(sK4,X5,sK5)
      | r3_orders_2(sK4,X4,sK5)
      | ~ r1_waybel_3(sK4,k12_lattice3(sK4,X4,X5),sK5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | v4_waybel_7(sK5,sK4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | r1_waybel_3(X0,k12_lattice3(X0,sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,
    ( r1_waybel_3(sK4,k12_lattice3(sK4,sK6,sK7),sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X2)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X3,X1)
                            & r2_hidden(X3,X2) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r3_orders_2(X0,X3,X1)
                  & r2_hidden(X3,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v4_waybel_7(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r3_orders_2(X0,X3,X1)
                  & r2_hidden(X3,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v4_waybel_7(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r3_orders_2(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( r3_orders_2(X0,sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(X0,sK3(X0,X1,X2),X1)
                & r2_hidden(sK3(X0,X1,X2),X2)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v4_waybel_7(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f45])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : v1_finset_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : v1_finset_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,
    ( ~ r3_orders_2(sK4,sK6,sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,sK3(X0,X1,X2),X1)
      | ~ r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,
    ( ~ r3_orders_2(sK4,sK7,sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,negated_conjecture,
    ( ~ v4_waybel_7(sK5,sK4)
    | m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5394,plain,
    ( v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( ~ v4_waybel_7(sK5,sK4)
    | m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_5395,plain,
    ( v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X2)) = k12_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_917,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X2)) = k12_lattice3(X1,X0,X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k12_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_40,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_922,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k12_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_40,c_39,c_35,c_33])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1,X0)) = k12_lattice3(sK4,X1,X0) ),
    inference(renaming,[status(thm)],[c_922])).

cnf(c_5392,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k12_lattice3(sK4,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_5835,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,sK7)) = k12_lattice3(sK4,X0,sK7)
    | v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_5392])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( ~ r3_orders_2(X0,sK2(X0,X1),X1)
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,negated_conjecture,
    ( v5_waybel_7(k1_waybel_4(sK4),sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_720,plain,
    ( ~ r3_orders_2(X0,sK2(X0,X1),X1)
    | v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k1_waybel_4(X0) != k1_waybel_4(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_721,plain,
    ( ~ r3_orders_2(sK4,sK2(sK4,X0),X0)
    | v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_37,negated_conjecture,
    ( v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( v3_waybel_3(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_725,plain,
    ( ~ r3_orders_2(sK4,sK2(sK4,X0),X0)
    | v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_19,plain,
    ( v4_waybel_7(X0,X1)
    | ~ v5_waybel_6(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_892,plain,
    ( v4_waybel_7(X0,X1)
    | ~ v5_waybel_6(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_893,plain,
    ( v4_waybel_7(X0,sK4)
    | ~ v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_892])).

cnf(c_897,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v5_waybel_6(X0,sK4)
    | v4_waybel_7(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_893,c_40,c_39,c_38,c_35,c_33])).

cnf(c_898,plain,
    ( v4_waybel_7(X0,sK4)
    | ~ v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_897])).

cnf(c_1051,plain,
    ( ~ r3_orders_2(sK4,sK2(sK4,X0),X0)
    | v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(resolution,[status(thm)],[c_725,c_898])).

cnf(c_3196,plain,
    ( ~ r3_orders_2(sK4,sK2(sK4,X0),X0)
    | v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1051])).

cnf(c_14,plain,
    ( ~ r3_orders_2(X0,sK1(X0,X1),X1)
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_696,plain,
    ( ~ r3_orders_2(X0,sK1(X0,X1),X1)
    | v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k1_waybel_4(X0) != k1_waybel_4(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_697,plain,
    ( ~ r3_orders_2(sK4,sK1(sK4,X0),X0)
    | v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_701,plain,
    ( ~ r3_orders_2(sK4,sK1(sK4,X0),X0)
    | v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_697,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1068,plain,
    ( ~ r3_orders_2(sK4,sK1(sK4,X0),X0)
    | v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(resolution,[status(thm)],[c_701,c_898])).

cnf(c_3192,plain,
    ( ~ r3_orders_2(sK4,sK1(sK4,X0),X0)
    | v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1068])).

cnf(c_30,negated_conjecture,
    ( ~ r1_waybel_3(sK4,k12_lattice3(sK4,X0,X1),sK5)
    | r3_orders_2(sK4,X0,sK5)
    | r3_orders_2(sK4,X1,sK5)
    | v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_15,plain,
    ( r1_waybel_3(X0,k12_lattice3(X0,sK1(X0,X1),sK2(X0,X1)),X1)
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_672,plain,
    ( r1_waybel_3(X0,k12_lattice3(X0,sK1(X0,X1),sK2(X0,X1)),X1)
    | v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k1_waybel_4(X0) != k1_waybel_4(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_673,plain,
    ( r1_waybel_3(sK4,k12_lattice3(sK4,sK1(sK4,X0),sK2(sK4,X0)),X0)
    | v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_677,plain,
    ( r1_waybel_3(sK4,k12_lattice3(sK4,sK1(sK4,X0),sK2(sK4,X0)),X0)
    | v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1085,plain,
    ( r1_waybel_3(sK4,k12_lattice3(sK4,sK1(sK4,X0),sK2(sK4,X0)),X0)
    | v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(resolution,[status(thm)],[c_677,c_898])).

cnf(c_1482,plain,
    ( r3_orders_2(sK4,X0,sK5)
    | r3_orders_2(sK4,X1,sK5)
    | v4_waybel_7(X2,sK4)
    | v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | k12_lattice3(sK4,sK1(sK4,X2),sK2(sK4,X2)) != k12_lattice3(sK4,X0,X1)
    | k1_waybel_4(sK4) != k1_waybel_4(sK4)
    | sK5 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1085])).

cnf(c_1483,plain,
    ( r3_orders_2(sK4,X0,sK5)
    | r3_orders_2(sK4,X1,sK5)
    | v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5)) != k12_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1482])).

cnf(c_1487,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v4_waybel_7(sK5,sK4)
    | r3_orders_2(sK4,X1,sK5)
    | r3_orders_2(sK4,X0,sK5)
    | k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5)) != k12_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1483,c_31])).

cnf(c_1488,plain,
    ( r3_orders_2(sK4,X0,sK5)
    | r3_orders_2(sK4,X1,sK5)
    | v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5)) != k12_lattice3(sK4,X0,X1) ),
    inference(renaming,[status(thm)],[c_1487])).

cnf(c_4852,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6111,plain,
    ( r3_orders_2(sK4,sK1(sK4,sK5),sK5)
    | r3_orders_2(sK4,sK2(sK4,sK5),sK5)
    | v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,sK5),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_1488,c_4852])).

cnf(c_17,plain,
    ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_624,plain,
    ( v5_waybel_6(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k1_waybel_4(X1) != k1_waybel_4(sK4)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_625,plain,
    ( v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_629,plain,
    ( v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1119,plain,
    ( v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(resolution,[status(thm)],[c_629,c_898])).

cnf(c_3184,plain,
    ( v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1119])).

cnf(c_5666,plain,
    ( v4_waybel_7(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3184])).

cnf(c_16,plain,
    ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_648,plain,
    ( v5_waybel_6(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k1_waybel_4(X1) != k1_waybel_4(sK4)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_649,plain,
    ( v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_653,plain,
    ( v5_waybel_6(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1102,plain,
    ( v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4) ),
    inference(resolution,[status(thm)],[c_653,c_898])).

cnf(c_3188,plain,
    ( v4_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1102])).

cnf(c_5669,plain,
    ( v4_waybel_7(sK5,sK4)
    | m1_subset_1(sK2(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3188])).

cnf(c_5746,plain,
    ( k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5)) = k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4852])).

cnf(c_5747,plain,
    ( r3_orders_2(sK4,sK1(sK4,sK5),sK5)
    | r3_orders_2(sK4,sK2(sK4,sK5),sK5)
    | v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,sK5),u1_struct_0(sK4))
    | k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5)) != k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_6188,plain,
    ( r3_orders_2(sK4,sK1(sK4,sK5),sK5)
    | r3_orders_2(sK4,sK2(sK4,sK5),sK5)
    | v4_waybel_7(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6111,c_31,c_5666,c_5669,c_5746,c_5747])).

cnf(c_6215,plain,
    ( r3_orders_2(sK4,sK2(sK4,sK5),sK5)
    | v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_3192,c_6188])).

cnf(c_6245,plain,
    ( v4_waybel_7(sK5,sK4)
    | r3_orders_2(sK4,sK2(sK4,sK5),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6215,c_31])).

cnf(c_6246,plain,
    ( r3_orders_2(sK4,sK2(sK4,sK5),sK5)
    | v4_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_6245])).

cnf(c_6269,plain,
    ( v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_3196,c_6246])).

cnf(c_6270,plain,
    ( v4_waybel_7(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6269])).

cnf(c_6344,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,sK7)) = k12_lattice3(sK4,X0,sK7)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5835,c_50,c_6270])).

cnf(c_6353,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK6,sK7)) = k12_lattice3(sK4,sK6,sK7)
    | v4_waybel_7(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5394,c_6344])).

cnf(c_6454,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK6,sK7)) = k12_lattice3(sK4,sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6353,c_50,c_6270])).

cnf(c_27,negated_conjecture,
    ( r1_waybel_3(sK4,k12_lattice3(sK4,sK6,sK7),sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_21,plain,
    ( ~ r1_waybel_3(X0,k2_yellow_0(X0,X1),X2)
    | ~ v4_waybel_7(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(sK3(X0,X2,X1),X1)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_802,plain,
    ( ~ r1_waybel_3(X0,k2_yellow_0(X0,X1),X2)
    | ~ v4_waybel_7(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(sK3(X0,X2,X1),X1)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_803,plain,
    ( ~ r1_waybel_3(sK4,k2_yellow_0(sK4,X0),X1)
    | ~ v4_waybel_7(X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK3(sK4,X1,X0),X0)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_807,plain,
    ( ~ r1_waybel_3(sK4,k2_yellow_0(sK4,X0),X1)
    | ~ v4_waybel_7(X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK3(sK4,X1,X0),X0)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_40,c_39,c_38,c_36,c_35,c_33])).

cnf(c_1422,plain,
    ( ~ v4_waybel_7(X0,sK4)
    | ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK3(sK4,X0,X1),X1)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X1)
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_807])).

cnf(c_1423,plain,
    ( ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,sK5,X0),X0)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1422])).

cnf(c_1427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_waybel_7(sK5,sK4)
    | r2_hidden(sK3(sK4,sK5,X0),X0)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1423,c_31])).

cnf(c_1428,plain,
    ( ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK3(sK4,sK5,X0),X0)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(renaming,[status(thm)],[c_1427])).

cnf(c_5389,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,sK5,X0),X0) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_6369,plain,
    ( v4_waybel_7(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6269,c_31])).

cnf(c_6381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK3(sK4,sK5,X0),X0)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6369,c_1428])).

cnf(c_6390,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,sK5,X0),X0) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6381])).

cnf(c_7185,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,sK5,X0),X0) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5389,c_6390])).

cnf(c_7198,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK4),sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,sK5,k7_domain_1(u1_struct_0(sK4),sK6,sK7)),k7_domain_1(u1_struct_0(sK4),sK6,sK7)) = iProver_top
    | v1_finset_1(k7_domain_1(u1_struct_0(sK4),sK6,sK7)) != iProver_top
    | v1_xboole_0(k7_domain_1(u1_struct_0(sK4),sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6454,c_7185])).

cnf(c_46,plain,
    ( v2_lattice3(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_48,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_54,plain,
    ( v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_55,plain,
    ( v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_99,plain,
    ( ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_98,plain,
    ( l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_100,plain,
    ( l1_struct_0(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_106,plain,
    ( l1_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_105,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_107,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_126,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_125,plain,
    ( l1_orders_2(X0) != iProver_top
    | v2_lattice3(X0) != iProver_top
    | v2_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_127,plain,
    ( l1_orders_2(sK4) != iProver_top
    | v2_lattice3(sK4) != iProver_top
    | v2_struct_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6154,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK4),sK6,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6590,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK4),sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6154])).

cnf(c_6591,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK4),sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6590])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6153,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),sK6,X0) = k2_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6608,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),sK6,sK7) = k2_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_6153])).

cnf(c_4859,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5811,plain,
    ( v1_finset_1(X0)
    | ~ v1_finset_1(k2_tarski(X1,X2))
    | X0 != k2_tarski(X1,X2) ),
    inference(instantiation,[status(thm)],[c_4859])).

cnf(c_6864,plain,
    ( v1_finset_1(k7_domain_1(u1_struct_0(sK4),sK6,sK7))
    | ~ v1_finset_1(k2_tarski(sK6,sK7))
    | k7_domain_1(u1_struct_0(sK4),sK6,sK7) != k2_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_5811])).

cnf(c_6865,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK6,sK7) != k2_tarski(sK6,sK7)
    | v1_finset_1(k7_domain_1(u1_struct_0(sK4),sK6,sK7)) = iProver_top
    | v1_finset_1(k2_tarski(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6864])).

cnf(c_10,plain,
    ( v1_finset_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8466,plain,
    ( v1_finset_1(k2_tarski(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8467,plain,
    ( v1_finset_1(k2_tarski(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8466])).

cnf(c_16239,plain,
    ( r2_hidden(sK3(sK4,sK5,k7_domain_1(u1_struct_0(sK4),sK6,sK7)),k7_domain_1(u1_struct_0(sK4),sK6,sK7)) = iProver_top
    | v1_xboole_0(k7_domain_1(u1_struct_0(sK4),sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7198,c_35,c_46,c_33,c_48,c_31,c_50,c_29,c_54,c_28,c_55,c_99,c_100,c_106,c_107,c_126,c_127,c_6269,c_6270,c_6591,c_6608,c_6865,c_8467])).

cnf(c_5399,plain,
    ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8337,plain,
    ( k7_domain_1(u1_struct_0(sK4),X0,sK7) = k2_tarski(X0,sK7)
    | v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_5399])).

cnf(c_8670,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | k7_domain_1(u1_struct_0(sK4),X0,sK7) = k2_tarski(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8337,c_46,c_48,c_50,c_100,c_107,c_127,c_6270])).

cnf(c_8671,plain,
    ( k7_domain_1(u1_struct_0(sK4),X0,sK7) = k2_tarski(X0,sK7)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8670])).

cnf(c_8679,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK6,sK7) = k2_tarski(sK6,sK7)
    | v4_waybel_7(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5394,c_8671])).

cnf(c_8805,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK6,sK7) = k2_tarski(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8679,c_35,c_33,c_31,c_29,c_28,c_99,c_106,c_126,c_6269,c_6608])).

cnf(c_16243,plain,
    ( r2_hidden(sK3(sK4,sK5,k2_tarski(sK6,sK7)),k2_tarski(sK6,sK7)) = iProver_top
    | v1_xboole_0(k2_tarski(sK6,sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16239,c_8805])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5400,plain,
    ( v1_xboole_0(k2_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16246,plain,
    ( r2_hidden(sK3(sK4,sK5,k2_tarski(sK6,sK7)),k2_tarski(sK6,sK7)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16243,c_5400])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_5404,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16248,plain,
    ( sK3(sK4,sK5,k2_tarski(sK6,sK7)) = sK6
    | sK3(sK4,sK5,k2_tarski(sK6,sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_16246,c_5404])).

cnf(c_8808,plain,
    ( k2_yellow_0(sK4,k2_tarski(sK6,sK7)) = k12_lattice3(sK4,sK6,sK7) ),
    inference(demodulation,[status(thm)],[c_8805,c_6454])).

cnf(c_22,plain,
    ( ~ r1_waybel_3(X0,k2_yellow_0(X0,X1),X2)
    | ~ v4_waybel_7(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_769,plain,
    ( ~ r1_waybel_3(X0,k2_yellow_0(X0,X1),X2)
    | ~ v4_waybel_7(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_770,plain,
    ( ~ r1_waybel_3(sK4,k2_yellow_0(sK4,X0),X1)
    | ~ v4_waybel_7(X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X1,X0),u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_774,plain,
    ( ~ r1_waybel_3(sK4,k2_yellow_0(sK4,X0),X1)
    | ~ v4_waybel_7(X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X1,X0),u1_struct_0(sK4))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_40,c_39,c_38,c_36,c_35,c_33])).

cnf(c_1452,plain,
    ( ~ v4_waybel_7(X0,sK4)
    | ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X1)
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_774])).

cnf(c_1453,plain,
    ( ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,sK5,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1452])).

cnf(c_1457,plain,
    ( m1_subset_1(sK3(sK4,sK5,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_waybel_7(sK5,sK4)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1453,c_31])).

cnf(c_1458,plain,
    ( ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,sK5,X0),u1_struct_0(sK4))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(renaming,[status(thm)],[c_1457])).

cnf(c_5388,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_1454,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_7501,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5388,c_50,c_1454,c_6270])).

cnf(c_10314,plain,
    ( m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK7)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k2_tarski(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_finset_1(k2_tarski(sK6,sK7)) != iProver_top
    | v1_xboole_0(k2_tarski(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8808,c_7501])).

cnf(c_5403,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) != iProver_top
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8809,plain,
    ( m1_subset_1(k2_tarski(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8805,c_5403])).

cnf(c_21911,plain,
    ( m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK7)),u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(k2_tarski(sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10314,c_46,c_48,c_50,c_54,c_55,c_100,c_107,c_127,c_6270,c_8467,c_8809])).

cnf(c_21917,plain,
    ( m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK7)),u1_struct_0(sK4)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21911,c_5400])).

cnf(c_8338,plain,
    ( k7_domain_1(u1_struct_0(sK4),X0,sK6) = k2_tarski(X0,sK6)
    | v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5394,c_5399])).

cnf(c_9021,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | k7_domain_1(u1_struct_0(sK4),X0,sK6) = k2_tarski(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8338,c_46,c_48,c_50,c_100,c_107,c_127,c_6270])).

cnf(c_9022,plain,
    ( k7_domain_1(u1_struct_0(sK4),X0,sK6) = k2_tarski(X0,sK6)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9021])).

cnf(c_21937,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK3(sK4,sK5,k2_tarski(sK6,sK7)),sK6) = k2_tarski(sK3(sK4,sK5,k2_tarski(sK6,sK7)),sK6) ),
    inference(superposition,[status(thm)],[c_21917,c_9022])).

cnf(c_22065,plain,
    ( sK3(sK4,sK5,k2_tarski(sK6,sK7)) = sK7
    | k2_tarski(sK3(sK4,sK5,k2_tarski(sK6,sK7)),sK6) = k7_domain_1(u1_struct_0(sK4),sK6,sK6) ),
    inference(superposition,[status(thm)],[c_16248,c_21937])).

cnf(c_9030,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK6,sK6) = k2_tarski(sK6,sK6)
    | v4_waybel_7(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5394,c_9022])).

cnf(c_6611,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),sK6,sK6) = k2_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_6153])).

cnf(c_9180,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK6,sK6) = k2_tarski(sK6,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9030,c_35,c_33,c_31,c_29,c_99,c_106,c_126,c_6269,c_6611])).

cnf(c_22077,plain,
    ( sK3(sK4,sK5,k2_tarski(sK6,sK7)) = sK7
    | k2_tarski(sK3(sK4,sK5,k2_tarski(sK6,sK7)),sK6) = k2_tarski(sK6,sK6) ),
    inference(light_normalisation,[status(thm)],[c_22065,c_9180])).

cnf(c_26,negated_conjecture,
    ( ~ r3_orders_2(sK4,sK6,sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_57,plain,
    ( r3_orders_2(sK4,sK6,sK5) != iProver_top
    | v4_waybel_7(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ r1_waybel_3(X0,k2_yellow_0(X0,X1),X2)
    | r3_orders_2(X0,sK3(X0,X2,X1),X2)
    | ~ v4_waybel_7(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_835,plain,
    ( ~ r1_waybel_3(X0,k2_yellow_0(X0,X1),X2)
    | r3_orders_2(X0,sK3(X0,X2,X1),X2)
    | ~ v4_waybel_7(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_836,plain,
    ( ~ r1_waybel_3(sK4,k2_yellow_0(sK4,X0),X1)
    | r3_orders_2(sK4,sK3(sK4,X1,X0),X1)
    | ~ v4_waybel_7(X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_840,plain,
    ( ~ r1_waybel_3(sK4,k2_yellow_0(sK4,X0),X1)
    | r3_orders_2(sK4,sK3(sK4,X1,X0),X1)
    | ~ v4_waybel_7(X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_836,c_40,c_39,c_38,c_36,c_35,c_33])).

cnf(c_1392,plain,
    ( r3_orders_2(sK4,sK3(sK4,X0,X1),X0)
    | ~ v4_waybel_7(X0,sK4)
    | ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X1)
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_840])).

cnf(c_1393,plain,
    ( r3_orders_2(sK4,sK3(sK4,sK5,X0),sK5)
    | ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1392])).

cnf(c_1397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_waybel_7(sK5,sK4)
    | r3_orders_2(sK4,sK3(sK4,sK5,X0),sK5)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1393,c_31])).

cnf(c_1398,plain,
    ( r3_orders_2(sK4,sK3(sK4,sK5,X0),sK5)
    | ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(renaming,[status(thm)],[c_1397])).

cnf(c_5390,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | r3_orders_2(sK4,sK3(sK4,sK5,X0),sK5) = iProver_top
    | v4_waybel_7(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1398])).

cnf(c_6380,plain,
    ( r3_orders_2(sK4,sK3(sK4,sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6369,c_1398])).

cnf(c_6393,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | r3_orders_2(sK4,sK3(sK4,sK5,X0),sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6380])).

cnf(c_7593,plain,
    ( r3_orders_2(sK4,sK3(sK4,sK5,X0),sK5) = iProver_top
    | k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5390,c_6393])).

cnf(c_7594,plain,
    ( k12_lattice3(sK4,sK6,sK7) != k2_yellow_0(sK4,X0)
    | r3_orders_2(sK4,sK3(sK4,sK5,X0),sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7593])).

cnf(c_10313,plain,
    ( r3_orders_2(sK4,sK3(sK4,sK5,k2_tarski(sK6,sK7)),sK5) = iProver_top
    | m1_subset_1(k2_tarski(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_finset_1(k2_tarski(sK6,sK7)) != iProver_top
    | v1_xboole_0(k2_tarski(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8808,c_7594])).

cnf(c_18500,plain,
    ( r3_orders_2(sK4,sK3(sK4,sK5,k2_tarski(sK6,sK7)),sK5) = iProver_top
    | v1_xboole_0(k2_tarski(sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10313,c_46,c_48,c_50,c_54,c_55,c_100,c_107,c_127,c_6270,c_8467,c_8809])).

cnf(c_18506,plain,
    ( r3_orders_2(sK4,sK3(sK4,sK5,k2_tarski(sK6,sK7)),sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18500,c_5400])).

cnf(c_18508,plain,
    ( sK3(sK4,sK5,k2_tarski(sK6,sK7)) = sK7
    | r3_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_16248,c_18506])).

cnf(c_23502,plain,
    ( sK3(sK4,sK5,k2_tarski(sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22077,c_50,c_57,c_6270,c_18508])).

cnf(c_23517,plain,
    ( r3_orders_2(sK4,sK7,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23502,c_18506])).

cnf(c_25,negated_conjecture,
    ( ~ r3_orders_2(sK4,sK7,sK5)
    | ~ v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5397,plain,
    ( r3_orders_2(sK4,sK7,sK5) != iProver_top
    | v4_waybel_7(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_58,plain,
    ( r3_orders_2(sK4,sK7,sK5) != iProver_top
    | v4_waybel_7(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2939,plain,
    ( ~ r3_orders_2(sK4,sK7,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4)
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1119])).

cnf(c_2940,plain,
    ( ~ r3_orders_2(sK4,sK7,sK5)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_2939])).

cnf(c_2941,plain,
    ( r3_orders_2(sK4,sK7,sK5) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2940])).

cnf(c_2953,plain,
    ( ~ r3_orders_2(sK4,sK7,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4)
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1102])).

cnf(c_2954,plain,
    ( ~ r3_orders_2(sK4,sK7,sK5)
    | m1_subset_1(sK2(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_2953])).

cnf(c_2955,plain,
    ( r3_orders_2(sK4,sK7,sK5) != iProver_top
    | m1_subset_1(sK2(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2954])).

cnf(c_2967,plain,
    ( ~ r3_orders_2(sK4,sK1(sK4,X0),X0)
    | ~ r3_orders_2(sK4,sK7,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4)
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1068])).

cnf(c_2968,plain,
    ( ~ r3_orders_2(sK4,sK1(sK4,sK5),sK5)
    | ~ r3_orders_2(sK4,sK7,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_2967])).

cnf(c_2969,plain,
    ( r3_orders_2(sK4,sK1(sK4,sK5),sK5) != iProver_top
    | r3_orders_2(sK4,sK7,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2968])).

cnf(c_2981,plain,
    ( ~ r3_orders_2(sK4,sK2(sK4,X0),X0)
    | ~ r3_orders_2(sK4,sK7,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_waybel_4(sK4) != k1_waybel_4(sK4)
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1051])).

cnf(c_2982,plain,
    ( ~ r3_orders_2(sK4,sK2(sK4,sK5),sK5)
    | ~ r3_orders_2(sK4,sK7,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_2981])).

cnf(c_2983,plain,
    ( r3_orders_2(sK4,sK2(sK4,sK5),sK5) != iProver_top
    | r3_orders_2(sK4,sK7,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2982])).

cnf(c_5748,plain,
    ( k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5)) != k12_lattice3(sK4,sK1(sK4,sK5),sK2(sK4,sK5))
    | r3_orders_2(sK4,sK1(sK4,sK5),sK5) = iProver_top
    | r3_orders_2(sK4,sK2(sK4,sK5),sK5) = iProver_top
    | v4_waybel_7(sK5,sK4) = iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5747])).

cnf(c_5754,plain,
    ( r3_orders_2(sK4,sK7,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5397,c_50,c_58,c_2941,c_2955,c_2969,c_2983,c_5746,c_5748])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23517,c_5754])).


%------------------------------------------------------------------------------
