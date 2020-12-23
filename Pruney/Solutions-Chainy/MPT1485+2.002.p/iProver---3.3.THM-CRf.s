%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:02 EST 2020

% Result     : Theorem 35.85s
% Output     : CNFRefutation 35.85s
% Verified   : 
% Statistics : Number of formulae       :  322 (1536 expanded)
%              Number of clauses        :  229 ( 423 expanded)
%              Number of leaves         :   27 ( 465 expanded)
%              Depth                    :   21
%              Number of atoms          : 2005 (10809 expanded)
%              Number of equality atoms :  404 (1651 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f56,f57])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK10)) != X1
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k12_lattice3(X0,sK9,k13_lattice3(X0,sK9,X2)) != sK9
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
              ( k12_lattice3(sK8,X1,k13_lattice3(sK8,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK8)) )
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & l1_orders_2(sK8)
      & v2_lattice3(sK8)
      & v1_lattice3(sK8)
      & v5_orders_2(sK8)
      & v3_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9
    & m1_subset_1(sK10,u1_struct_0(sK8))
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l1_orders_2(sK8)
    & v2_lattice3(sK8)
    & v1_lattice3(sK8)
    & v5_orders_2(sK8)
    & v3_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f37,f61,f60,f59])).

fof(f101,plain,(
    v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
                        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f38,plain,(
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

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f47,plain,(
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
            ( r1_orders_2(X0,sK5(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK5(X0,X5,X6))
        & r1_orders_2(X0,X5,sK5(X0,X5,X6))
        & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK4(X0,X3))
        & r1_orders_2(X0,X2,sK4(X0,X3))
        & r1_orders_2(X0,X1,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
                & r1_orders_2(X0,sK3(X0),X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK3(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
                    & r1_orders_2(X0,sK2(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK2(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,X3,sK4(X0,X3))
                & r1_orders_2(X0,sK3(X0),sK4(X0,X3))
                & r1_orders_2(X0,sK2(X0),sK4(X0,X3))
                & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK3(X0),X3)
              | ~ r1_orders_2(X0,sK2(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK3(X0),u1_struct_0(X0))
          & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,sK5(X0,X5,X6),X8)
                      | ~ r1_orders_2(X0,X6,X8)
                      | ~ r1_orders_2(X0,X5,X8)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X6,sK5(X0,X5,X6))
                  & r1_orders_2(X0,X5,sK5(X0,X5,X6))
                  & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f47,f46,f45,f44])).

fof(f71,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK5(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK5(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f62])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
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
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK5(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f105,plain,(
    k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
    inference(cnf_transformation,[],[f62])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f21,f39,f38])).

fof(f78,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_276,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_1])).

cnf(c_277,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_39,negated_conjecture,
    ( v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_586,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_277,c_39])).

cnf(c_587,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_41,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_38,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_591,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_41,c_38])).

cnf(c_3117,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | ~ r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_591])).

cnf(c_107860,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | ~ r1_orders_2(sK8,sK7(sK8,X1_53,k10_lattice3(sK8,sK9,sK10),X0_53),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_53,k10_lattice3(sK8,sK9,sK10)) = X0_53 ),
    inference(instantiation,[status(thm)],[c_3117])).

cnf(c_107877,plain,
    ( ~ r1_orders_2(sK8,sK7(sK8,sK9,k10_lattice3(sK8,sK9,sK10),sK9),sK9)
    | ~ r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | ~ r1_orders_2(sK8,sK9,sK9)
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = sK9 ),
    inference(instantiation,[status(thm)],[c_107860])).

cnf(c_27,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_264,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_1])).

cnf(c_265,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_652,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_265,c_39])).

cnf(c_653,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_655,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_41,c_38])).

cnf(c_3115,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_655])).

cnf(c_107862,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | r1_orders_2(sK8,sK7(sK8,X1_53,k10_lattice3(sK8,sK9,sK10),X0_53),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_53,k10_lattice3(sK8,sK9,sK10)) = X0_53 ),
    inference(instantiation,[status(thm)],[c_3115])).

cnf(c_107869,plain,
    ( r1_orders_2(sK8,sK7(sK8,sK9,k10_lattice3(sK8,sK9,sK10),sK9),sK9)
    | ~ r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | ~ r1_orders_2(sK8,sK9,sK9)
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = sK9 ),
    inference(instantiation,[status(thm)],[c_107862])).

cnf(c_3134,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_96752,plain,
    ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) != X1_53
    | sK9 != X1_53
    | sK9 = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_96754,plain,
    ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != sK9
    | sK9 = k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_96752])).

cnf(c_24,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_283,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_0])).

cnf(c_284,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_1101,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_41])).

cnf(c_1102,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_1101])).

cnf(c_40,negated_conjecture,
    ( v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1104,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1102,c_40,c_38])).

cnf(c_1105,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_1104])).

cnf(c_3104,plain,
    ( r1_orders_2(sK8,X0_53,k10_lattice3(sK8,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1105])).

cnf(c_95307,plain,
    ( r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3104])).

cnf(c_92361,plain,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != X0_53
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = sK9
    | sK9 != X0_53 ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_95215,plain,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = sK9
    | sK9 != k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_92361])).

cnf(c_95216,plain,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = sK9
    | sK9 != k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_95215])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK5(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3125,plain,
    ( ~ r1_orders_2(X0_52,X0_53,X1_53)
    | ~ r1_orders_2(X0_52,X2_53,X1_53)
    | r1_orders_2(X0_52,sK5(X0_52,X2_53,X0_53),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_94076,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
    | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
    | ~ r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_3125])).

cnf(c_94078,plain,
    ( r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) = iProver_top
    | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_94076])).

cnf(c_94080,plain,
    ( r1_orders_2(sK8,sK5(sK8,sK10,sK9),sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) = iProver_top
    | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) != iProver_top
    | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_94078])).

cnf(c_12,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3124,plain,
    ( r1_orders_2(X0_52,X0_53,sK5(X0_52,X1_53,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_73184,plain,
    ( r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_3124])).

cnf(c_73185,plain,
    ( r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X0_53)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73184])).

cnf(c_73187,plain,
    ( r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_73185])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3119,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_3674,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3119])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_39])).

cnf(c_792,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X0,X1) = k12_lattice3(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_796,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X0,X1) = k12_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_792,c_41,c_38])).

cnf(c_3113,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X0_53,X1_53) = k12_lattice3(sK8,X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_796])).

cnf(c_3680,plain,
    ( k11_lattice3(sK8,X0_53,X1_53) = k12_lattice3(sK8,X0_53,X1_53)
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3113])).

cnf(c_5183,plain,
    ( k11_lattice3(sK8,sK9,X0_53) = k12_lattice3(sK8,sK9,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_3680])).

cnf(c_6055,plain,
    ( k11_lattice3(sK8,sK9,sK9) = k12_lattice3(sK8,sK9,sK9) ),
    inference(superposition,[status(thm)],[c_3674,c_5183])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1210,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_38])).

cnf(c_1211,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1210])).

cnf(c_3101,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1211])).

cnf(c_3692,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3101])).

cnf(c_7921,plain,
    ( m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6055,c_3692])).

cnf(c_48,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_812,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_813,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(k12_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(k12_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_813,c_41,c_38])).

cnf(c_3112,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | m1_subset_1(k12_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_817])).

cnf(c_3179,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k12_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3112])).

cnf(c_3181,plain,
    ( m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3179])).

cnf(c_8898,plain,
    ( m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7921,c_48,c_3181])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1121,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_41])).

cnf(c_1122,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1121])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1122,c_40,c_38])).

cnf(c_3103,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | k13_lattice3(sK8,X0_53,X1_53) = k10_lattice3(sK8,X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_1126])).

cnf(c_3690,plain,
    ( k13_lattice3(sK8,X0_53,X1_53) = k10_lattice3(sK8,X0_53,X1_53)
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3103])).

cnf(c_8910,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),X0_53) = k10_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8898,c_3690])).

cnf(c_69814,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9) = k10_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9) ),
    inference(superposition,[status(thm)],[c_3674,c_8910])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_42,negated_conjecture,
    ( v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_42])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ v2_lattice3(sK8)
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | k13_lattice3(sK8,k12_lattice3(sK8,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k13_lattice3(sK8,k12_lattice3(sK8,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_41,c_40,c_39,c_38])).

cnf(c_3118,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | k13_lattice3(sK8,k12_lattice3(sK8,X0_53,X1_53),X1_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_566])).

cnf(c_3675,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,X0_53,X1_53),X1_53) = X1_53
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3118])).

cnf(c_4062,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,X0_53),X0_53) = X0_53
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_3675])).

cnf(c_4629,plain,
    ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_3674,c_4062])).

cnf(c_69825,plain,
    ( k10_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_69814,c_4629])).

cnf(c_23,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_290,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_0])).

cnf(c_291,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_1077,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_291,c_41])).

cnf(c_1078,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_1077])).

cnf(c_1082,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1078,c_40,c_38])).

cnf(c_1083,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_1082])).

cnf(c_3105,plain,
    ( r1_orders_2(sK8,X0_53,k10_lattice3(sK8,X1_53,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1_53,X0_53),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1083])).

cnf(c_3688,plain,
    ( r1_orders_2(sK8,X0_53,k10_lattice3(sK8,X1_53,X0_53)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X1_53,X0_53),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3105])).

cnf(c_71243,plain,
    ( r1_orders_2(sK8,sK9,k10_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9)) = iProver_top
    | m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_69825,c_3688])).

cnf(c_71246,plain,
    ( r1_orders_2(sK8,sK9,sK9) = iProver_top
    | m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_71243,c_69825])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3123,plain,
    ( r1_orders_2(X0_52,X0_53,sK5(X0_52,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_63821,plain,
    ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_3123])).

cnf(c_63822,plain,
    ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63821])).

cnf(c_63824,plain,
    ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63822])).

cnf(c_20,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_309,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_0])).

cnf(c_310,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_309])).

cnf(c_982,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_310,c_41])).

cnf(c_983,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_985,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_983,c_40,c_38])).

cnf(c_986,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_985])).

cnf(c_3108,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | r1_orders_2(sK8,X2_53,sK6(sK8,X2_53,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_986])).

cnf(c_21308,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | r1_orders_2(sK8,X0_53,sK6(sK8,X0_53,sK10,X1_53))
    | ~ r1_orders_2(sK8,sK10,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_53,sK10) = X1_53 ),
    inference(instantiation,[status(thm)],[c_3108])).

cnf(c_43138,plain,
    ( r1_orders_2(sK8,X0_53,sK6(sK8,X0_53,sK10,sK5(sK8,sK10,X1_53)))
    | ~ r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X1_53))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK10,X1_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_53,sK10) = sK5(sK8,sK10,X1_53) ),
    inference(instantiation,[status(thm)],[c_21308])).

cnf(c_43139,plain,
    ( k10_lattice3(sK8,X0_53,sK10) = sK5(sK8,sK10,X1_53)
    | r1_orders_2(sK8,X0_53,sK6(sK8,X0_53,sK10,sK5(sK8,sK10,X1_53))) = iProver_top
    | r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X1_53)) != iProver_top
    | r1_orders_2(sK8,sK10,sK5(sK8,sK10,X1_53)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK10,X1_53),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43138])).

cnf(c_43141,plain,
    ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9)
    | r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) != iProver_top
    | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) = iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top
    | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43139])).

cnf(c_18,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_321,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_0])).

cnf(c_322,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_321])).

cnf(c_916,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_322,c_41])).

cnf(c_917,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_921,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_917,c_40,c_38])).

cnf(c_922,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_921])).

cnf(c_3110,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | ~ r1_orders_2(sK8,X1_53,sK6(sK8,X2_53,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_922])).

cnf(c_11172,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK10,X0_53)
    | ~ r1_orders_2(sK8,sK9,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_3110])).

cnf(c_18129,plain,
    ( ~ r1_orders_2(sK8,sK5(sK8,X0_53,X1_53),sK6(sK8,sK9,sK10,sK5(sK8,X0_53,X1_53)))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,X0_53,X1_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,X0_53,X1_53))
    | ~ m1_subset_1(sK5(sK8,X0_53,X1_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_11172])).

cnf(c_25323,plain,
    ( ~ r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_18129])).

cnf(c_25324,plain,
    ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53)
    | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) != iProver_top
    | r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53)) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53)) != iProver_top
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25323])).

cnf(c_25326,plain,
    ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9)
    | r1_orders_2(sK8,sK5(sK8,sK10,sK9),sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) != iProver_top
    | r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top
    | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25324])).

cnf(c_19,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_316,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_0])).

cnf(c_317,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_949,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_41])).

cnf(c_950,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_954,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_950,c_40,c_38])).

cnf(c_955,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_954])).

cnf(c_3109,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | r1_orders_2(sK8,X0_53,sK6(sK8,X2_53,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_955])).

cnf(c_11173,plain,
    ( ~ r1_orders_2(sK8,sK10,X0_53)
    | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK9,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
    inference(instantiation,[status(thm)],[c_3109])).

cnf(c_18303,plain,
    ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,X0_53,X1_53)))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,X0_53,X1_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,X0_53,X1_53))
    | ~ m1_subset_1(sK5(sK8,X0_53,X1_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_11173])).

cnf(c_24902,plain,
    ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
    | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_18303])).

cnf(c_24903,plain,
    ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53)
    | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) = iProver_top
    | r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53)) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53)) != iProver_top
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24902])).

cnf(c_24905,plain,
    ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9)
    | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) = iProver_top
    | r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top
    | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24903])).

cnf(c_21,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_302,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_0])).

cnf(c_303,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_302])).

cnf(c_1011,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_303,c_41])).

cnf(c_1012,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X2,X0,X1),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1011])).

cnf(c_1016,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X2,X0,X1),u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1012,c_40,c_38])).

cnf(c_1017,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X2,X0,X1),u1_struct_0(sK8))
    | k10_lattice3(sK8,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1016])).

cnf(c_3107,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X2_53,X0_53,X1_53),u1_struct_0(sK8))
    | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_1017])).

cnf(c_4996,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK5(sK8,X1_53,X2_53))
    | ~ r1_orders_2(sK8,X3_53,sK5(sK8,X1_53,X2_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_53,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X3_53,X0_53,sK5(sK8,X1_53,X2_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,X1_53,X2_53),u1_struct_0(sK8))
    | k10_lattice3(sK8,X3_53,X0_53) = sK5(sK8,X1_53,X2_53) ),
    inference(instantiation,[status(thm)],[c_3107])).

cnf(c_11201,plain,
    ( ~ r1_orders_2(sK8,sK10,sK5(sK8,X0_53,X1_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,X0_53,X1_53))
    | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,X0_53,X1_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,X0_53,X1_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_4996])).

cnf(c_24115,plain,
    ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
    | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
    | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_11201])).

cnf(c_24116,plain,
    ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53)
    | r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53)) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53)) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24115])).

cnf(c_24118,plain,
    ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9)
    | r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24116])).

cnf(c_22666,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_3113])).

cnf(c_22668,plain,
    ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22666])).

cnf(c_22670,plain,
    ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22668])).

cnf(c_5566,plain,
    ( X0_53 != X1_53
    | X0_53 = k11_lattice3(sK8,X2_53,X3_53)
    | k11_lattice3(sK8,X2_53,X3_53) != X1_53 ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_17751,plain,
    ( k11_lattice3(sK8,X0_53,X1_53) != X2_53
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != X2_53
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_5566])).

cnf(c_18461,plain,
    ( k11_lattice3(sK8,X0_53,X1_53) != k12_lattice3(sK8,X2_53,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,X1_53)
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,X2_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_17751])).

cnf(c_22665,plain,
    ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_18461])).

cnf(c_22667,plain,
    ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_22665])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3122,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | m1_subset_1(sK5(X0_52,X1_53,X0_53),u1_struct_0(X0_52))
    | ~ sP0(X0_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_11248,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_3122])).

cnf(c_11249,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11248])).

cnf(c_11251,plain,
    ( m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11249])).

cnf(c_11250,plain,
    ( m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_11248])).

cnf(c_3136,plain,
    ( ~ m1_subset_1(X0_53,X0_54)
    | m1_subset_1(X1_53,X0_54)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_3754,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,X1_53,X2_53),u1_struct_0(sK8))
    | k10_lattice3(sK8,X1_53,X2_53) != X0_53 ),
    inference(instantiation,[status(thm)],[c_3136])).

cnf(c_4281,plain,
    ( m1_subset_1(k10_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,X1_53,X2_53),u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_53,X1_53) != sK5(sK8,X1_53,X2_53) ),
    inference(instantiation,[status(thm)],[c_3754])).

cnf(c_8955,plain,
    ( m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53) ),
    inference(instantiation,[status(thm)],[c_4281])).

cnf(c_8956,plain,
    ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53)
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8955])).

cnf(c_8958,plain,
    ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,sK9)
    | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8956])).

cnf(c_8957,plain,
    ( m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
    | k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_8955])).

cnf(c_26,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_271,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_1])).

cnf(c_272,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_271])).

cnf(c_619,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_272,c_39])).

cnf(c_620,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_624,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_620,c_41,c_38])).

cnf(c_3116,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X0_53,X2_53)
    | r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X2_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_624])).

cnf(c_3677,plain,
    ( k11_lattice3(sK8,X0_53,X1_53) = X2_53
    | r1_orders_2(sK8,X2_53,X0_53) != iProver_top
    | r1_orders_2(sK8,X2_53,X1_53) != iProver_top
    | r1_orders_2(sK8,sK7(sK8,X0_53,X1_53,X2_53),X1_53) = iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3116])).

cnf(c_3676,plain,
    ( k11_lattice3(sK8,X0_53,X1_53) = X2_53
    | r1_orders_2(sK8,X2_53,X0_53) != iProver_top
    | r1_orders_2(sK8,X2_53,X1_53) != iProver_top
    | r1_orders_2(sK8,sK7(sK8,X0_53,X1_53,X2_53),X2_53) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3117])).

cnf(c_8069,plain,
    ( k11_lattice3(sK8,X0_53,X1_53) = X1_53
    | r1_orders_2(sK8,X1_53,X0_53) != iProver_top
    | r1_orders_2(sK8,X1_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3677,c_3676])).

cnf(c_8071,plain,
    ( k11_lattice3(sK8,sK9,sK9) = sK9
    | r1_orders_2(sK8,sK9,sK9) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8069])).

cnf(c_3135,plain,
    ( X0_53 != X1_53
    | X2_53 != X3_53
    | k12_lattice3(X0_52,X0_53,X2_53) = k12_lattice3(X0_52,X1_53,X3_53) ),
    theory(equality)).

cnf(c_5165,plain,
    ( k13_lattice3(sK8,sK9,sK10) != X0_53
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X1_53,X0_53)
    | sK9 != X1_53 ),
    inference(instantiation,[status(thm)],[c_3135])).

cnf(c_7629,plain,
    ( k13_lattice3(sK8,sK9,sK10) != k10_lattice3(sK8,sK9,sK10)
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
    | sK9 != X0_53 ),
    inference(instantiation,[status(thm)],[c_5165])).

cnf(c_7630,plain,
    ( k13_lattice3(sK8,sK9,sK10) != k10_lattice3(sK8,sK9,sK10)
    | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_7629])).

cnf(c_5567,plain,
    ( k11_lattice3(sK8,sK9,sK9) != sK9
    | sK9 = k11_lattice3(sK8,sK9,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_5566])).

cnf(c_5140,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k13_lattice3(sK8,sK9,sK10) = k10_lattice3(sK8,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_3103])).

cnf(c_3137,plain,
    ( ~ r1_orders_2(X0_52,X0_53,X1_53)
    | r1_orders_2(X0_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_3773,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | r1_orders_2(sK8,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    inference(instantiation,[status(thm)],[c_3137])).

cnf(c_3994,plain,
    ( r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_53,X3_53),X3_53)
    | X1_53 != X3_53
    | X0_53 != k11_lattice3(sK8,X2_53,X3_53) ),
    inference(instantiation,[status(thm)],[c_3773])).

cnf(c_3996,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK9),sK9)
    | r1_orders_2(sK8,sK9,sK9)
    | sK9 != k11_lattice3(sK8,sK9,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_3994])).

cnf(c_31,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_238,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_1])).

cnf(c_239,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_771,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_39])).

cnf(c_772,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_774,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_41,c_38])).

cnf(c_775,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_774])).

cnf(c_1229,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1211,c_775])).

cnf(c_3099,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_53,X1_53),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1229])).

cnf(c_3213,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK9),sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3099])).

cnf(c_35,negated_conjecture,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3121,negated_conjecture,
    ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_3133,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_3144,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_4,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_130,plain,
    ( sP1(X0) != iProver_top
    | sP0(X0) = iProver_top
    | v1_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_132,plain,
    ( sP1(sK8) != iProver_top
    | sP0(sK8) = iProver_top
    | v1_lattice3(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_131,plain,
    ( ~ sP1(sK8)
    | sP0(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( sP1(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_99,plain,
    ( sP1(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_101,plain,
    ( sP1(sK8) = iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_100,plain,
    ( sP1(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_49,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_47,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_45,plain,
    ( v1_lattice3(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_107877,c_107869,c_96754,c_95307,c_95216,c_94080,c_73187,c_71246,c_63824,c_43141,c_25326,c_24905,c_24118,c_22670,c_22667,c_11251,c_11250,c_8958,c_8957,c_8071,c_7630,c_5567,c_5140,c_3996,c_3213,c_3181,c_3121,c_3144,c_132,c_131,c_101,c_100,c_49,c_36,c_48,c_37,c_47,c_38,c_45,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.85/5.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.85/5.01  
% 35.85/5.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.85/5.01  
% 35.85/5.01  ------  iProver source info
% 35.85/5.01  
% 35.85/5.01  git: date: 2020-06-30 10:37:57 +0100
% 35.85/5.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.85/5.01  git: non_committed_changes: false
% 35.85/5.01  git: last_make_outside_of_git: false
% 35.85/5.01  
% 35.85/5.01  ------ 
% 35.85/5.01  
% 35.85/5.01  ------ Input Options
% 35.85/5.01  
% 35.85/5.01  --out_options                           all
% 35.85/5.01  --tptp_safe_out                         true
% 35.85/5.01  --problem_path                          ""
% 35.85/5.01  --include_path                          ""
% 35.85/5.01  --clausifier                            res/vclausify_rel
% 35.85/5.01  --clausifier_options                    ""
% 35.85/5.01  --stdin                                 false
% 35.85/5.01  --stats_out                             all
% 35.85/5.01  
% 35.85/5.01  ------ General Options
% 35.85/5.01  
% 35.85/5.01  --fof                                   false
% 35.85/5.01  --time_out_real                         305.
% 35.85/5.01  --time_out_virtual                      -1.
% 35.85/5.01  --symbol_type_check                     false
% 35.85/5.01  --clausify_out                          false
% 35.85/5.01  --sig_cnt_out                           false
% 35.85/5.01  --trig_cnt_out                          false
% 35.85/5.01  --trig_cnt_out_tolerance                1.
% 35.85/5.01  --trig_cnt_out_sk_spl                   false
% 35.85/5.01  --abstr_cl_out                          false
% 35.85/5.01  
% 35.85/5.01  ------ Global Options
% 35.85/5.01  
% 35.85/5.01  --schedule                              default
% 35.85/5.01  --add_important_lit                     false
% 35.85/5.01  --prop_solver_per_cl                    1000
% 35.85/5.01  --min_unsat_core                        false
% 35.85/5.01  --soft_assumptions                      false
% 35.85/5.01  --soft_lemma_size                       3
% 35.85/5.01  --prop_impl_unit_size                   0
% 35.85/5.01  --prop_impl_unit                        []
% 35.85/5.01  --share_sel_clauses                     true
% 35.85/5.01  --reset_solvers                         false
% 35.85/5.01  --bc_imp_inh                            [conj_cone]
% 35.85/5.01  --conj_cone_tolerance                   3.
% 35.85/5.01  --extra_neg_conj                        none
% 35.85/5.01  --large_theory_mode                     true
% 35.85/5.01  --prolific_symb_bound                   200
% 35.85/5.01  --lt_threshold                          2000
% 35.85/5.01  --clause_weak_htbl                      true
% 35.85/5.01  --gc_record_bc_elim                     false
% 35.85/5.01  
% 35.85/5.01  ------ Preprocessing Options
% 35.85/5.01  
% 35.85/5.01  --preprocessing_flag                    true
% 35.85/5.01  --time_out_prep_mult                    0.1
% 35.85/5.01  --splitting_mode                        input
% 35.85/5.01  --splitting_grd                         true
% 35.85/5.01  --splitting_cvd                         false
% 35.85/5.01  --splitting_cvd_svl                     false
% 35.85/5.01  --splitting_nvd                         32
% 35.85/5.01  --sub_typing                            true
% 35.85/5.01  --prep_gs_sim                           true
% 35.85/5.01  --prep_unflatten                        true
% 35.85/5.01  --prep_res_sim                          true
% 35.85/5.01  --prep_upred                            true
% 35.85/5.01  --prep_sem_filter                       exhaustive
% 35.85/5.01  --prep_sem_filter_out                   false
% 35.85/5.01  --pred_elim                             true
% 35.85/5.01  --res_sim_input                         true
% 35.85/5.01  --eq_ax_congr_red                       true
% 35.85/5.01  --pure_diseq_elim                       true
% 35.85/5.01  --brand_transform                       false
% 35.85/5.01  --non_eq_to_eq                          false
% 35.85/5.01  --prep_def_merge                        true
% 35.85/5.01  --prep_def_merge_prop_impl              false
% 35.85/5.01  --prep_def_merge_mbd                    true
% 35.85/5.01  --prep_def_merge_tr_red                 false
% 35.85/5.01  --prep_def_merge_tr_cl                  false
% 35.85/5.01  --smt_preprocessing                     true
% 35.85/5.01  --smt_ac_axioms                         fast
% 35.85/5.01  --preprocessed_out                      false
% 35.85/5.01  --preprocessed_stats                    false
% 35.85/5.01  
% 35.85/5.01  ------ Abstraction refinement Options
% 35.85/5.01  
% 35.85/5.01  --abstr_ref                             []
% 35.85/5.01  --abstr_ref_prep                        false
% 35.85/5.01  --abstr_ref_until_sat                   false
% 35.85/5.01  --abstr_ref_sig_restrict                funpre
% 35.85/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.85/5.01  --abstr_ref_under                       []
% 35.85/5.01  
% 35.85/5.01  ------ SAT Options
% 35.85/5.01  
% 35.85/5.01  --sat_mode                              false
% 35.85/5.01  --sat_fm_restart_options                ""
% 35.85/5.01  --sat_gr_def                            false
% 35.85/5.01  --sat_epr_types                         true
% 35.85/5.01  --sat_non_cyclic_types                  false
% 35.85/5.01  --sat_finite_models                     false
% 35.85/5.01  --sat_fm_lemmas                         false
% 35.85/5.01  --sat_fm_prep                           false
% 35.85/5.01  --sat_fm_uc_incr                        true
% 35.85/5.01  --sat_out_model                         small
% 35.85/5.01  --sat_out_clauses                       false
% 35.85/5.01  
% 35.85/5.01  ------ QBF Options
% 35.85/5.01  
% 35.85/5.01  --qbf_mode                              false
% 35.85/5.01  --qbf_elim_univ                         false
% 35.85/5.01  --qbf_dom_inst                          none
% 35.85/5.01  --qbf_dom_pre_inst                      false
% 35.85/5.01  --qbf_sk_in                             false
% 35.85/5.01  --qbf_pred_elim                         true
% 35.85/5.01  --qbf_split                             512
% 35.85/5.01  
% 35.85/5.01  ------ BMC1 Options
% 35.85/5.01  
% 35.85/5.01  --bmc1_incremental                      false
% 35.85/5.01  --bmc1_axioms                           reachable_all
% 35.85/5.01  --bmc1_min_bound                        0
% 35.85/5.01  --bmc1_max_bound                        -1
% 35.85/5.01  --bmc1_max_bound_default                -1
% 35.85/5.01  --bmc1_symbol_reachability              true
% 35.85/5.01  --bmc1_property_lemmas                  false
% 35.85/5.01  --bmc1_k_induction                      false
% 35.85/5.01  --bmc1_non_equiv_states                 false
% 35.85/5.01  --bmc1_deadlock                         false
% 35.85/5.01  --bmc1_ucm                              false
% 35.85/5.01  --bmc1_add_unsat_core                   none
% 35.85/5.01  --bmc1_unsat_core_children              false
% 35.85/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.85/5.01  --bmc1_out_stat                         full
% 35.85/5.01  --bmc1_ground_init                      false
% 35.85/5.01  --bmc1_pre_inst_next_state              false
% 35.85/5.01  --bmc1_pre_inst_state                   false
% 35.85/5.01  --bmc1_pre_inst_reach_state             false
% 35.85/5.01  --bmc1_out_unsat_core                   false
% 35.85/5.01  --bmc1_aig_witness_out                  false
% 35.85/5.01  --bmc1_verbose                          false
% 35.85/5.01  --bmc1_dump_clauses_tptp                false
% 35.85/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.85/5.01  --bmc1_dump_file                        -
% 35.85/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.85/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.85/5.01  --bmc1_ucm_extend_mode                  1
% 35.85/5.01  --bmc1_ucm_init_mode                    2
% 35.85/5.01  --bmc1_ucm_cone_mode                    none
% 35.85/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.85/5.01  --bmc1_ucm_relax_model                  4
% 35.85/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.85/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.85/5.01  --bmc1_ucm_layered_model                none
% 35.85/5.01  --bmc1_ucm_max_lemma_size               10
% 35.85/5.01  
% 35.85/5.01  ------ AIG Options
% 35.85/5.01  
% 35.85/5.01  --aig_mode                              false
% 35.85/5.01  
% 35.85/5.01  ------ Instantiation Options
% 35.85/5.01  
% 35.85/5.01  --instantiation_flag                    true
% 35.85/5.01  --inst_sos_flag                         true
% 35.85/5.01  --inst_sos_phase                        true
% 35.85/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.85/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.85/5.01  --inst_lit_sel_side                     num_symb
% 35.85/5.01  --inst_solver_per_active                1400
% 35.85/5.01  --inst_solver_calls_frac                1.
% 35.85/5.01  --inst_passive_queue_type               priority_queues
% 35.85/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.85/5.01  --inst_passive_queues_freq              [25;2]
% 35.85/5.01  --inst_dismatching                      true
% 35.85/5.01  --inst_eager_unprocessed_to_passive     true
% 35.85/5.01  --inst_prop_sim_given                   true
% 35.85/5.01  --inst_prop_sim_new                     false
% 35.85/5.01  --inst_subs_new                         false
% 35.85/5.01  --inst_eq_res_simp                      false
% 35.85/5.01  --inst_subs_given                       false
% 35.85/5.01  --inst_orphan_elimination               true
% 35.85/5.01  --inst_learning_loop_flag               true
% 35.85/5.01  --inst_learning_start                   3000
% 35.85/5.01  --inst_learning_factor                  2
% 35.85/5.01  --inst_start_prop_sim_after_learn       3
% 35.85/5.01  --inst_sel_renew                        solver
% 35.85/5.01  --inst_lit_activity_flag                true
% 35.85/5.01  --inst_restr_to_given                   false
% 35.85/5.01  --inst_activity_threshold               500
% 35.85/5.01  --inst_out_proof                        true
% 35.85/5.01  
% 35.85/5.01  ------ Resolution Options
% 35.85/5.01  
% 35.85/5.01  --resolution_flag                       true
% 35.85/5.01  --res_lit_sel                           adaptive
% 35.85/5.01  --res_lit_sel_side                      none
% 35.85/5.01  --res_ordering                          kbo
% 35.85/5.01  --res_to_prop_solver                    active
% 35.85/5.01  --res_prop_simpl_new                    false
% 35.85/5.01  --res_prop_simpl_given                  true
% 35.85/5.01  --res_passive_queue_type                priority_queues
% 35.85/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.85/5.01  --res_passive_queues_freq               [15;5]
% 35.85/5.01  --res_forward_subs                      full
% 35.85/5.01  --res_backward_subs                     full
% 35.85/5.01  --res_forward_subs_resolution           true
% 35.85/5.01  --res_backward_subs_resolution          true
% 35.85/5.01  --res_orphan_elimination                true
% 35.85/5.01  --res_time_limit                        2.
% 35.85/5.01  --res_out_proof                         true
% 35.85/5.01  
% 35.85/5.01  ------ Superposition Options
% 35.85/5.01  
% 35.85/5.01  --superposition_flag                    true
% 35.85/5.01  --sup_passive_queue_type                priority_queues
% 35.85/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.85/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.85/5.01  --demod_completeness_check              fast
% 35.85/5.01  --demod_use_ground                      true
% 35.85/5.01  --sup_to_prop_solver                    passive
% 35.85/5.01  --sup_prop_simpl_new                    true
% 35.85/5.01  --sup_prop_simpl_given                  true
% 35.85/5.01  --sup_fun_splitting                     true
% 35.85/5.01  --sup_smt_interval                      50000
% 35.85/5.01  
% 35.85/5.01  ------ Superposition Simplification Setup
% 35.85/5.01  
% 35.85/5.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.85/5.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.85/5.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.85/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.85/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.85/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.85/5.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.85/5.01  --sup_immed_triv                        [TrivRules]
% 35.85/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/5.01  --sup_immed_bw_main                     []
% 35.85/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.85/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.85/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/5.01  --sup_input_bw                          []
% 35.85/5.01  
% 35.85/5.01  ------ Combination Options
% 35.85/5.01  
% 35.85/5.01  --comb_res_mult                         3
% 35.85/5.01  --comb_sup_mult                         2
% 35.85/5.01  --comb_inst_mult                        10
% 35.85/5.01  
% 35.85/5.01  ------ Debug Options
% 35.85/5.01  
% 35.85/5.01  --dbg_backtrace                         false
% 35.85/5.01  --dbg_dump_prop_clauses                 false
% 35.85/5.01  --dbg_dump_prop_clauses_file            -
% 35.85/5.01  --dbg_out_stat                          false
% 35.85/5.01  ------ Parsing...
% 35.85/5.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.85/5.01  
% 35.85/5.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 35.85/5.01  
% 35.85/5.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.85/5.01  
% 35.85/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.85/5.01  ------ Proving...
% 35.85/5.01  ------ Problem Properties 
% 35.85/5.01  
% 35.85/5.01  
% 35.85/5.01  clauses                                 34
% 35.85/5.01  conjectures                             3
% 35.85/5.01  EPR                                     1
% 35.85/5.01  Horn                                    23
% 35.85/5.01  unary                                   4
% 35.85/5.01  binary                                  2
% 35.85/5.01  lits                                    148
% 35.85/5.01  lits eq                                 13
% 35.85/5.01  fd_pure                                 0
% 35.85/5.01  fd_pseudo                               0
% 35.85/5.01  fd_cond                                 0
% 35.85/5.01  fd_pseudo_cond                          8
% 35.85/5.01  AC symbols                              0
% 35.85/5.01  
% 35.85/5.01  ------ Schedule dynamic 5 is on 
% 35.85/5.01  
% 35.85/5.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.85/5.01  
% 35.85/5.01  
% 35.85/5.01  ------ 
% 35.85/5.01  Current options:
% 35.85/5.01  ------ 
% 35.85/5.01  
% 35.85/5.01  ------ Input Options
% 35.85/5.01  
% 35.85/5.01  --out_options                           all
% 35.85/5.01  --tptp_safe_out                         true
% 35.85/5.01  --problem_path                          ""
% 35.85/5.01  --include_path                          ""
% 35.85/5.01  --clausifier                            res/vclausify_rel
% 35.85/5.01  --clausifier_options                    ""
% 35.85/5.01  --stdin                                 false
% 35.85/5.01  --stats_out                             all
% 35.85/5.01  
% 35.85/5.01  ------ General Options
% 35.85/5.01  
% 35.85/5.01  --fof                                   false
% 35.85/5.01  --time_out_real                         305.
% 35.85/5.01  --time_out_virtual                      -1.
% 35.85/5.01  --symbol_type_check                     false
% 35.85/5.01  --clausify_out                          false
% 35.85/5.01  --sig_cnt_out                           false
% 35.85/5.01  --trig_cnt_out                          false
% 35.85/5.01  --trig_cnt_out_tolerance                1.
% 35.85/5.01  --trig_cnt_out_sk_spl                   false
% 35.85/5.01  --abstr_cl_out                          false
% 35.85/5.01  
% 35.85/5.01  ------ Global Options
% 35.85/5.01  
% 35.85/5.01  --schedule                              default
% 35.85/5.01  --add_important_lit                     false
% 35.85/5.01  --prop_solver_per_cl                    1000
% 35.85/5.01  --min_unsat_core                        false
% 35.85/5.01  --soft_assumptions                      false
% 35.85/5.01  --soft_lemma_size                       3
% 35.85/5.01  --prop_impl_unit_size                   0
% 35.85/5.01  --prop_impl_unit                        []
% 35.85/5.01  --share_sel_clauses                     true
% 35.85/5.01  --reset_solvers                         false
% 35.85/5.01  --bc_imp_inh                            [conj_cone]
% 35.85/5.01  --conj_cone_tolerance                   3.
% 35.85/5.01  --extra_neg_conj                        none
% 35.85/5.01  --large_theory_mode                     true
% 35.85/5.01  --prolific_symb_bound                   200
% 35.85/5.01  --lt_threshold                          2000
% 35.85/5.01  --clause_weak_htbl                      true
% 35.85/5.01  --gc_record_bc_elim                     false
% 35.85/5.01  
% 35.85/5.01  ------ Preprocessing Options
% 35.85/5.01  
% 35.85/5.01  --preprocessing_flag                    true
% 35.85/5.01  --time_out_prep_mult                    0.1
% 35.85/5.01  --splitting_mode                        input
% 35.85/5.01  --splitting_grd                         true
% 35.85/5.01  --splitting_cvd                         false
% 35.85/5.01  --splitting_cvd_svl                     false
% 35.85/5.01  --splitting_nvd                         32
% 35.85/5.01  --sub_typing                            true
% 35.85/5.01  --prep_gs_sim                           true
% 35.85/5.01  --prep_unflatten                        true
% 35.85/5.01  --prep_res_sim                          true
% 35.85/5.01  --prep_upred                            true
% 35.85/5.01  --prep_sem_filter                       exhaustive
% 35.85/5.01  --prep_sem_filter_out                   false
% 35.85/5.01  --pred_elim                             true
% 35.85/5.01  --res_sim_input                         true
% 35.85/5.01  --eq_ax_congr_red                       true
% 35.85/5.01  --pure_diseq_elim                       true
% 35.85/5.01  --brand_transform                       false
% 35.85/5.01  --non_eq_to_eq                          false
% 35.85/5.01  --prep_def_merge                        true
% 35.85/5.01  --prep_def_merge_prop_impl              false
% 35.85/5.01  --prep_def_merge_mbd                    true
% 35.85/5.01  --prep_def_merge_tr_red                 false
% 35.85/5.01  --prep_def_merge_tr_cl                  false
% 35.85/5.01  --smt_preprocessing                     true
% 35.85/5.01  --smt_ac_axioms                         fast
% 35.85/5.01  --preprocessed_out                      false
% 35.85/5.01  --preprocessed_stats                    false
% 35.85/5.01  
% 35.85/5.01  ------ Abstraction refinement Options
% 35.85/5.01  
% 35.85/5.01  --abstr_ref                             []
% 35.85/5.01  --abstr_ref_prep                        false
% 35.85/5.01  --abstr_ref_until_sat                   false
% 35.85/5.01  --abstr_ref_sig_restrict                funpre
% 35.85/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.85/5.01  --abstr_ref_under                       []
% 35.85/5.01  
% 35.85/5.01  ------ SAT Options
% 35.85/5.01  
% 35.85/5.01  --sat_mode                              false
% 35.85/5.01  --sat_fm_restart_options                ""
% 35.85/5.01  --sat_gr_def                            false
% 35.85/5.01  --sat_epr_types                         true
% 35.85/5.01  --sat_non_cyclic_types                  false
% 35.85/5.01  --sat_finite_models                     false
% 35.85/5.01  --sat_fm_lemmas                         false
% 35.85/5.01  --sat_fm_prep                           false
% 35.85/5.01  --sat_fm_uc_incr                        true
% 35.85/5.01  --sat_out_model                         small
% 35.85/5.01  --sat_out_clauses                       false
% 35.85/5.01  
% 35.85/5.01  ------ QBF Options
% 35.85/5.01  
% 35.85/5.01  --qbf_mode                              false
% 35.85/5.01  --qbf_elim_univ                         false
% 35.85/5.01  --qbf_dom_inst                          none
% 35.85/5.01  --qbf_dom_pre_inst                      false
% 35.85/5.01  --qbf_sk_in                             false
% 35.85/5.01  --qbf_pred_elim                         true
% 35.85/5.01  --qbf_split                             512
% 35.85/5.01  
% 35.85/5.01  ------ BMC1 Options
% 35.85/5.01  
% 35.85/5.01  --bmc1_incremental                      false
% 35.85/5.01  --bmc1_axioms                           reachable_all
% 35.85/5.01  --bmc1_min_bound                        0
% 35.85/5.01  --bmc1_max_bound                        -1
% 35.85/5.01  --bmc1_max_bound_default                -1
% 35.85/5.01  --bmc1_symbol_reachability              true
% 35.85/5.01  --bmc1_property_lemmas                  false
% 35.85/5.01  --bmc1_k_induction                      false
% 35.85/5.01  --bmc1_non_equiv_states                 false
% 35.85/5.01  --bmc1_deadlock                         false
% 35.85/5.01  --bmc1_ucm                              false
% 35.85/5.01  --bmc1_add_unsat_core                   none
% 35.85/5.01  --bmc1_unsat_core_children              false
% 35.85/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.85/5.01  --bmc1_out_stat                         full
% 35.85/5.01  --bmc1_ground_init                      false
% 35.85/5.01  --bmc1_pre_inst_next_state              false
% 35.85/5.01  --bmc1_pre_inst_state                   false
% 35.85/5.01  --bmc1_pre_inst_reach_state             false
% 35.85/5.01  --bmc1_out_unsat_core                   false
% 35.85/5.01  --bmc1_aig_witness_out                  false
% 35.85/5.01  --bmc1_verbose                          false
% 35.85/5.01  --bmc1_dump_clauses_tptp                false
% 35.85/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.85/5.01  --bmc1_dump_file                        -
% 35.85/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.85/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.85/5.01  --bmc1_ucm_extend_mode                  1
% 35.85/5.01  --bmc1_ucm_init_mode                    2
% 35.85/5.01  --bmc1_ucm_cone_mode                    none
% 35.85/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.85/5.01  --bmc1_ucm_relax_model                  4
% 35.85/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.85/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.85/5.01  --bmc1_ucm_layered_model                none
% 35.85/5.01  --bmc1_ucm_max_lemma_size               10
% 35.85/5.01  
% 35.85/5.01  ------ AIG Options
% 35.85/5.01  
% 35.85/5.01  --aig_mode                              false
% 35.85/5.01  
% 35.85/5.01  ------ Instantiation Options
% 35.85/5.01  
% 35.85/5.01  --instantiation_flag                    true
% 35.85/5.01  --inst_sos_flag                         true
% 35.85/5.01  --inst_sos_phase                        true
% 35.85/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.85/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.85/5.01  --inst_lit_sel_side                     none
% 35.85/5.01  --inst_solver_per_active                1400
% 35.85/5.01  --inst_solver_calls_frac                1.
% 35.85/5.01  --inst_passive_queue_type               priority_queues
% 35.85/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.85/5.01  --inst_passive_queues_freq              [25;2]
% 35.85/5.01  --inst_dismatching                      true
% 35.85/5.01  --inst_eager_unprocessed_to_passive     true
% 35.85/5.01  --inst_prop_sim_given                   true
% 35.85/5.01  --inst_prop_sim_new                     false
% 35.85/5.01  --inst_subs_new                         false
% 35.85/5.01  --inst_eq_res_simp                      false
% 35.85/5.01  --inst_subs_given                       false
% 35.85/5.01  --inst_orphan_elimination               true
% 35.85/5.01  --inst_learning_loop_flag               true
% 35.85/5.01  --inst_learning_start                   3000
% 35.85/5.01  --inst_learning_factor                  2
% 35.85/5.01  --inst_start_prop_sim_after_learn       3
% 35.85/5.01  --inst_sel_renew                        solver
% 35.85/5.01  --inst_lit_activity_flag                true
% 35.85/5.01  --inst_restr_to_given                   false
% 35.85/5.01  --inst_activity_threshold               500
% 35.85/5.01  --inst_out_proof                        true
% 35.85/5.01  
% 35.85/5.01  ------ Resolution Options
% 35.85/5.01  
% 35.85/5.01  --resolution_flag                       false
% 35.85/5.01  --res_lit_sel                           adaptive
% 35.85/5.01  --res_lit_sel_side                      none
% 35.85/5.01  --res_ordering                          kbo
% 35.85/5.01  --res_to_prop_solver                    active
% 35.85/5.01  --res_prop_simpl_new                    false
% 35.85/5.01  --res_prop_simpl_given                  true
% 35.85/5.01  --res_passive_queue_type                priority_queues
% 35.85/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.85/5.01  --res_passive_queues_freq               [15;5]
% 35.85/5.01  --res_forward_subs                      full
% 35.85/5.01  --res_backward_subs                     full
% 35.85/5.01  --res_forward_subs_resolution           true
% 35.85/5.01  --res_backward_subs_resolution          true
% 35.85/5.01  --res_orphan_elimination                true
% 35.85/5.01  --res_time_limit                        2.
% 35.85/5.01  --res_out_proof                         true
% 35.85/5.01  
% 35.85/5.01  ------ Superposition Options
% 35.85/5.01  
% 35.85/5.01  --superposition_flag                    true
% 35.85/5.01  --sup_passive_queue_type                priority_queues
% 35.85/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.85/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.85/5.01  --demod_completeness_check              fast
% 35.85/5.01  --demod_use_ground                      true
% 35.85/5.01  --sup_to_prop_solver                    passive
% 35.85/5.01  --sup_prop_simpl_new                    true
% 35.85/5.01  --sup_prop_simpl_given                  true
% 35.85/5.01  --sup_fun_splitting                     true
% 35.85/5.01  --sup_smt_interval                      50000
% 35.85/5.01  
% 35.85/5.01  ------ Superposition Simplification Setup
% 35.85/5.01  
% 35.85/5.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.85/5.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.85/5.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.85/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.85/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.85/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.85/5.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.85/5.01  --sup_immed_triv                        [TrivRules]
% 35.85/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/5.01  --sup_immed_bw_main                     []
% 35.85/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.85/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.85/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/5.01  --sup_input_bw                          []
% 35.85/5.01  
% 35.85/5.01  ------ Combination Options
% 35.85/5.01  
% 35.85/5.01  --comb_res_mult                         3
% 35.85/5.01  --comb_sup_mult                         2
% 35.85/5.01  --comb_inst_mult                        10
% 35.85/5.01  
% 35.85/5.01  ------ Debug Options
% 35.85/5.01  
% 35.85/5.01  --dbg_backtrace                         false
% 35.85/5.01  --dbg_dump_prop_clauses                 false
% 35.85/5.01  --dbg_dump_prop_clauses_file            -
% 35.85/5.01  --dbg_out_stat                          false
% 35.85/5.01  
% 35.85/5.01  
% 35.85/5.01  
% 35.85/5.01  
% 35.85/5.01  ------ Proving...
% 35.85/5.01  
% 35.85/5.01  
% 35.85/5.01  % SZS status Theorem for theBenchmark.p
% 35.85/5.01  
% 35.85/5.01  % SZS output start CNFRefutation for theBenchmark.p
% 35.85/5.01  
% 35.85/5.01  fof(f8,axiom,(
% 35.85/5.01    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f28,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 35.85/5.01    inference(ennf_transformation,[],[f8])).
% 35.85/5.01  
% 35.85/5.01  fof(f29,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(flattening,[],[f28])).
% 35.85/5.01  
% 35.85/5.01  fof(f54,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(nnf_transformation,[],[f29])).
% 35.85/5.01  
% 35.85/5.01  fof(f55,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(flattening,[],[f54])).
% 35.85/5.01  
% 35.85/5.01  fof(f56,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(rectify,[],[f55])).
% 35.85/5.01  
% 35.85/5.01  fof(f57,plain,(
% 35.85/5.01    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))))),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f58,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f56,f57])).
% 35.85/5.01  
% 35.85/5.01  fof(f94,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f58])).
% 35.85/5.01  
% 35.85/5.01  fof(f2,axiom,(
% 35.85/5.01    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f16,plain,(
% 35.85/5.01    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 35.85/5.01    inference(ennf_transformation,[],[f2])).
% 35.85/5.01  
% 35.85/5.01  fof(f17,plain,(
% 35.85/5.01    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f16])).
% 35.85/5.01  
% 35.85/5.01  fof(f64,plain,(
% 35.85/5.01    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f17])).
% 35.85/5.01  
% 35.85/5.01  fof(f12,conjecture,(
% 35.85/5.01    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f13,negated_conjecture,(
% 35.85/5.01    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 35.85/5.01    inference(negated_conjecture,[],[f12])).
% 35.85/5.01  
% 35.85/5.01  fof(f36,plain,(
% 35.85/5.01    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 35.85/5.01    inference(ennf_transformation,[],[f13])).
% 35.85/5.01  
% 35.85/5.01  fof(f37,plain,(
% 35.85/5.01    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f36])).
% 35.85/5.01  
% 35.85/5.01  fof(f61,plain,(
% 35.85/5.01    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK10)) != X1 & m1_subset_1(sK10,u1_struct_0(X0)))) )),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f60,plain,(
% 35.85/5.01    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK9,k13_lattice3(X0,sK9,X2)) != sK9 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f59,plain,(
% 35.85/5.01    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK8,X1,k13_lattice3(sK8,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK8))) & m1_subset_1(X1,u1_struct_0(sK8))) & l1_orders_2(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v3_orders_2(sK8))),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f62,plain,(
% 35.85/5.01    ((k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 & m1_subset_1(sK10,u1_struct_0(sK8))) & m1_subset_1(sK9,u1_struct_0(sK8))) & l1_orders_2(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v3_orders_2(sK8)),
% 35.85/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f37,f61,f60,f59])).
% 35.85/5.01  
% 35.85/5.01  fof(f101,plain,(
% 35.85/5.01    v2_lattice3(sK8)),
% 35.85/5.01    inference(cnf_transformation,[],[f62])).
% 35.85/5.01  
% 35.85/5.01  fof(f99,plain,(
% 35.85/5.01    v5_orders_2(sK8)),
% 35.85/5.01    inference(cnf_transformation,[],[f62])).
% 35.85/5.01  
% 35.85/5.01  fof(f102,plain,(
% 35.85/5.01    l1_orders_2(sK8)),
% 35.85/5.01    inference(cnf_transformation,[],[f62])).
% 35.85/5.01  
% 35.85/5.01  fof(f92,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f58])).
% 35.85/5.01  
% 35.85/5.01  fof(f7,axiom,(
% 35.85/5.01    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f26,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 35.85/5.01    inference(ennf_transformation,[],[f7])).
% 35.85/5.01  
% 35.85/5.01  fof(f27,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(flattening,[],[f26])).
% 35.85/5.01  
% 35.85/5.01  fof(f49,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(nnf_transformation,[],[f27])).
% 35.85/5.01  
% 35.85/5.01  fof(f50,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(flattening,[],[f49])).
% 35.85/5.01  
% 35.85/5.01  fof(f51,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(rectify,[],[f50])).
% 35.85/5.01  
% 35.85/5.01  fof(f52,plain,(
% 35.85/5.01    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))))),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f53,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.85/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).
% 35.85/5.01  
% 35.85/5.01  fof(f81,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f53])).
% 35.85/5.01  
% 35.85/5.01  fof(f108,plain,(
% 35.85/5.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(equality_resolution,[],[f81])).
% 35.85/5.01  
% 35.85/5.01  fof(f1,axiom,(
% 35.85/5.01    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f14,plain,(
% 35.85/5.01    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 35.85/5.01    inference(ennf_transformation,[],[f1])).
% 35.85/5.01  
% 35.85/5.01  fof(f15,plain,(
% 35.85/5.01    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f14])).
% 35.85/5.01  
% 35.85/5.01  fof(f63,plain,(
% 35.85/5.01    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f15])).
% 35.85/5.01  
% 35.85/5.01  fof(f100,plain,(
% 35.85/5.01    v1_lattice3(sK8)),
% 35.85/5.01    inference(cnf_transformation,[],[f62])).
% 35.85/5.01  
% 35.85/5.01  fof(f38,plain,(
% 35.85/5.01    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))))),
% 35.85/5.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 35.85/5.01  
% 35.85/5.01  fof(f42,plain,(
% 35.85/5.01    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~sP0(X0)))),
% 35.85/5.01    inference(nnf_transformation,[],[f38])).
% 35.85/5.01  
% 35.85/5.01  fof(f43,plain,(
% 35.85/5.01    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X5] : (! [X6] : (? [X7] : (! [X8] : (r1_orders_2(X0,X7,X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,X7) & r1_orders_2(X0,X5,X7) & m1_subset_1(X7,u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 35.85/5.01    inference(rectify,[],[f42])).
% 35.85/5.01  
% 35.85/5.01  fof(f47,plain,(
% 35.85/5.01    ! [X6,X5,X0] : (? [X7] : (! [X8] : (r1_orders_2(X0,X7,X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,X7) & r1_orders_2(X0,X5,X7) & m1_subset_1(X7,u1_struct_0(X0))) => (! [X8] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,sK5(X0,X5,X6)) & r1_orders_2(X0,X5,sK5(X0,X5,X6)) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))))),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f46,plain,(
% 35.85/5.01    ( ! [X2,X1] : (! [X3,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK4(X0,X3)) & r1_orders_2(X0,X2,sK4(X0,X3)) & r1_orders_2(X0,X1,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))) )),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f45,plain,(
% 35.85/5.01    ( ! [X1] : (! [X0] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,sK3(X0),X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,sK3(X0),X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))) )),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f44,plain,(
% 35.85/5.01    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,sK2(X0),X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,sK2(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 35.85/5.01    introduced(choice_axiom,[])).
% 35.85/5.01  
% 35.85/5.01  fof(f48,plain,(
% 35.85/5.01    ! [X0] : ((sP0(X0) | ((! [X3] : ((~r1_orders_2(X0,X3,sK4(X0,X3)) & r1_orders_2(X0,sK3(X0),sK4(X0,X3)) & r1_orders_2(X0,sK2(X0),sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,sK3(X0),X3) | ~r1_orders_2(X0,sK2(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X5] : (! [X6] : ((! [X8] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) & r1_orders_2(X0,X6,sK5(X0,X5,X6)) & r1_orders_2(X0,X5,sK5(X0,X5,X6)) & m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0)))),
% 35.85/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f47,f46,f45,f44])).
% 35.85/5.01  
% 35.85/5.01  fof(f71,plain,(
% 35.85/5.01    ( ! [X6,X0,X8,X5] : (r1_orders_2(X0,sK5(X0,X5,X6),X8) | ~r1_orders_2(X0,X6,X8) | ~r1_orders_2(X0,X5,X8) | ~m1_subset_1(X8,u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f48])).
% 35.85/5.01  
% 35.85/5.01  fof(f70,plain,(
% 35.85/5.01    ( ! [X6,X0,X5] : (r1_orders_2(X0,X6,sK5(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f48])).
% 35.85/5.01  
% 35.85/5.01  fof(f103,plain,(
% 35.85/5.01    m1_subset_1(sK9,u1_struct_0(sK8))),
% 35.85/5.01    inference(cnf_transformation,[],[f62])).
% 35.85/5.01  
% 35.85/5.01  fof(f9,axiom,(
% 35.85/5.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f30,plain,(
% 35.85/5.01    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 35.85/5.01    inference(ennf_transformation,[],[f9])).
% 35.85/5.01  
% 35.85/5.01  fof(f31,plain,(
% 35.85/5.01    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f30])).
% 35.85/5.01  
% 35.85/5.01  fof(f95,plain,(
% 35.85/5.01    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f31])).
% 35.85/5.01  
% 35.85/5.01  fof(f5,axiom,(
% 35.85/5.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f22,plain,(
% 35.85/5.01    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 35.85/5.01    inference(ennf_transformation,[],[f5])).
% 35.85/5.01  
% 35.85/5.01  fof(f23,plain,(
% 35.85/5.01    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f22])).
% 35.85/5.01  
% 35.85/5.01  fof(f79,plain,(
% 35.85/5.01    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f23])).
% 35.85/5.01  
% 35.85/5.01  fof(f6,axiom,(
% 35.85/5.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f24,plain,(
% 35.85/5.01    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 35.85/5.01    inference(ennf_transformation,[],[f6])).
% 35.85/5.01  
% 35.85/5.01  fof(f25,plain,(
% 35.85/5.01    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f24])).
% 35.85/5.01  
% 35.85/5.01  fof(f80,plain,(
% 35.85/5.01    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f25])).
% 35.85/5.01  
% 35.85/5.01  fof(f10,axiom,(
% 35.85/5.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f32,plain,(
% 35.85/5.01    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 35.85/5.01    inference(ennf_transformation,[],[f10])).
% 35.85/5.01  
% 35.85/5.01  fof(f33,plain,(
% 35.85/5.01    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f32])).
% 35.85/5.01  
% 35.85/5.01  fof(f96,plain,(
% 35.85/5.01    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f33])).
% 35.85/5.01  
% 35.85/5.01  fof(f11,axiom,(
% 35.85/5.01    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f34,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 35.85/5.01    inference(ennf_transformation,[],[f11])).
% 35.85/5.01  
% 35.85/5.01  fof(f35,plain,(
% 35.85/5.01    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f34])).
% 35.85/5.01  
% 35.85/5.01  fof(f97,plain,(
% 35.85/5.01    ( ! [X2,X0,X1] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f35])).
% 35.85/5.01  
% 35.85/5.01  fof(f98,plain,(
% 35.85/5.01    v3_orders_2(sK8)),
% 35.85/5.01    inference(cnf_transformation,[],[f62])).
% 35.85/5.01  
% 35.85/5.01  fof(f82,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f53])).
% 35.85/5.01  
% 35.85/5.01  fof(f107,plain,(
% 35.85/5.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(equality_resolution,[],[f82])).
% 35.85/5.01  
% 35.85/5.01  fof(f69,plain,(
% 35.85/5.01    ( ! [X6,X0,X5] : (r1_orders_2(X0,X5,sK5(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f48])).
% 35.85/5.01  
% 35.85/5.01  fof(f85,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X1,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f53])).
% 35.85/5.01  
% 35.85/5.01  fof(f87,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f53])).
% 35.85/5.01  
% 35.85/5.01  fof(f86,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f53])).
% 35.85/5.01  
% 35.85/5.01  fof(f84,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f53])).
% 35.85/5.01  
% 35.85/5.01  fof(f68,plain,(
% 35.85/5.01    ( ! [X6,X0,X5] : (m1_subset_1(sK5(X0,X5,X6),u1_struct_0(X0)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~sP0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f48])).
% 35.85/5.01  
% 35.85/5.01  fof(f93,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f58])).
% 35.85/5.01  
% 35.85/5.01  fof(f88,plain,(
% 35.85/5.01    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f58])).
% 35.85/5.01  
% 35.85/5.01  fof(f111,plain,(
% 35.85/5.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.85/5.01    inference(equality_resolution,[],[f88])).
% 35.85/5.01  
% 35.85/5.01  fof(f105,plain,(
% 35.85/5.01    k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9),
% 35.85/5.01    inference(cnf_transformation,[],[f62])).
% 35.85/5.01  
% 35.85/5.01  fof(f39,plain,(
% 35.85/5.01    ! [X0] : ((v1_lattice3(X0) <=> sP0(X0)) | ~sP1(X0))),
% 35.85/5.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 35.85/5.01  
% 35.85/5.01  fof(f41,plain,(
% 35.85/5.01    ! [X0] : (((v1_lattice3(X0) | ~sP0(X0)) & (sP0(X0) | ~v1_lattice3(X0))) | ~sP1(X0))),
% 35.85/5.01    inference(nnf_transformation,[],[f39])).
% 35.85/5.01  
% 35.85/5.01  fof(f66,plain,(
% 35.85/5.01    ( ! [X0] : (sP0(X0) | ~v1_lattice3(X0) | ~sP1(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f41])).
% 35.85/5.01  
% 35.85/5.01  fof(f4,axiom,(
% 35.85/5.01    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 35.85/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.85/5.01  
% 35.85/5.01  fof(f20,plain,(
% 35.85/5.01    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 35.85/5.01    inference(ennf_transformation,[],[f4])).
% 35.85/5.01  
% 35.85/5.01  fof(f21,plain,(
% 35.85/5.01    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 35.85/5.01    inference(flattening,[],[f20])).
% 35.85/5.01  
% 35.85/5.01  fof(f40,plain,(
% 35.85/5.01    ! [X0] : (sP1(X0) | ~l1_orders_2(X0))),
% 35.85/5.01    inference(definition_folding,[],[f21,f39,f38])).
% 35.85/5.01  
% 35.85/5.01  fof(f78,plain,(
% 35.85/5.01    ( ! [X0] : (sP1(X0) | ~l1_orders_2(X0)) )),
% 35.85/5.01    inference(cnf_transformation,[],[f40])).
% 35.85/5.01  
% 35.85/5.01  fof(f104,plain,(
% 35.85/5.01    m1_subset_1(sK10,u1_struct_0(sK8))),
% 35.85/5.01    inference(cnf_transformation,[],[f62])).
% 35.85/5.01  
% 35.85/5.01  cnf(c_25,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | v2_struct_0(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(cnf_transformation,[],[f94]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1,plain,
% 35.85/5.01      ( ~ v2_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f64]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_276,plain,
% 35.85/5.01      ( ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_25,c_1]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_277,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_276]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_39,negated_conjecture,
% 35.85/5.01      ( v2_lattice3(sK8) ),
% 35.85/5.01      inference(cnf_transformation,[],[f101]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_586,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | ~ r1_orders_2(X0,sK7(X0,X3,X2,X1),X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_277,c_39]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_587,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0,X2)
% 35.85/5.01      | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ v5_orders_2(sK8)
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | k11_lattice3(sK8,X1,X2) = X0 ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_586]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_41,negated_conjecture,
% 35.85/5.01      ( v5_orders_2(sK8) ),
% 35.85/5.01      inference(cnf_transformation,[],[f99]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_38,negated_conjecture,
% 35.85/5.01      ( l1_orders_2(sK8) ),
% 35.85/5.01      inference(cnf_transformation,[],[f102]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_591,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0,X2)
% 35.85/5.01      | ~ r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X0)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X1,X2) = X0 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_587,c_41,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3117,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X0_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_591]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_107860,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK7(sK8,X1_53,k10_lattice3(sK8,sK9,sK10),X0_53),X0_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X1_53,k10_lattice3(sK8,sK9,sK10)) = X0_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3117]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_107877,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,sK7(sK8,sK9,k10_lattice3(sK8,sK9,sK10),sK9),sK9)
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,sK9)
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = sK9 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_107860]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_27,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | v2_struct_0(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(cnf_transformation,[],[f92]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_264,plain,
% 35.85/5.01      ( ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_27,c_1]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_265,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_264]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_652,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X3)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_265,c_39]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_653,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0,X2)
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ v5_orders_2(sK8)
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | k11_lattice3(sK8,X1,X2) = X0 ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_652]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_655,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0,X2)
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X1,X2) = X0 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_653,c_41,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3115,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X1_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_655]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_107862,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X1_53,k10_lattice3(sK8,sK9,sK10),X0_53),X1_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X1_53,k10_lattice3(sK8,sK9,sK10)) = X0_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3115]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_107869,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK7(sK8,sK9,k10_lattice3(sK8,sK9,sK10),sK9),sK9)
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,sK9)
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = sK9 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_107862]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3134,plain,
% 35.85/5.01      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 35.85/5.01      theory(equality) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_96752,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) != X1_53
% 35.85/5.01      | sK9 != X1_53
% 35.85/5.01      | sK9 = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3134]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_96754,plain,
% 35.85/5.01      ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != sK9
% 35.85/5.01      | sK9 = k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | sK9 != sK9 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_96752]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_24,plain,
% 35.85/5.01      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | v2_struct_0(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f108]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_0,plain,
% 35.85/5.01      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f63]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_283,plain,
% 35.85/5.01      ( ~ v1_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_24,c_0]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_284,plain,
% 35.85/5.01      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0) ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_283]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1101,plain,
% 35.85/5.01      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_284,c_41]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1102,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8))
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | ~ v1_lattice3(sK8) ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_1101]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_40,negated_conjecture,
% 35.85/5.01      ( v1_lattice3(sK8) ),
% 35.85/5.01      inference(cnf_transformation,[],[f100]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1104,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_1102,c_40,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1105,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_1104]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3104,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0_53,k10_lattice3(sK8,X0_53,X1_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_1105]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_95307,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3104]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_92361,plain,
% 35.85/5.01      ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != X0_53
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = sK9
% 35.85/5.01      | sK9 != X0_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3134]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_95215,plain,
% 35.85/5.01      ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = sK9
% 35.85/5.01      | sK9 != k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_92361]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_95216,plain,
% 35.85/5.01      ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = sK9
% 35.85/5.01      | sK9 != k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_95215]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_11,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | r1_orders_2(X0,sK5(X0,X3,X1),X2)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ sP0(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f71]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3125,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0_52,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(X0_52,X2_53,X1_53)
% 35.85/5.01      | r1_orders_2(X0_52,sK5(X0_52,X2_53,X0_53),X1_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 35.85/5.01      | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
% 35.85/5.01      | ~ sP0(X0_52) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_11]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_94076,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
% 35.85/5.01      | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ sP0(sK8) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3125]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_94078,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) = iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) != iProver_top
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | sP0(sK8) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_94076]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_94080,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK5(sK8,sK10,sK9),sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) = iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) != iProver_top
% 35.85/5.01      | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | sP0(sK8) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_94078]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_12,plain,
% 35.85/5.01      ( r1_orders_2(X0,X1,sK5(X0,X2,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ sP0(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f70]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3124,plain,
% 35.85/5.01      ( r1_orders_2(X0_52,X0_53,sK5(X0_52,X1_53,X0_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 35.85/5.01      | ~ sP0(X0_52) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_12]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_73184,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X0_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ sP0(sK8) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3124]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_73185,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X0_53)) = iProver_top
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | sP0(sK8) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_73184]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_73187,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | sP0(sK8) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_73185]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_37,negated_conjecture,
% 35.85/5.01      ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 35.85/5.01      inference(cnf_transformation,[],[f103]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3119,negated_conjecture,
% 35.85/5.01      ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_37]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3674,plain,
% 35.85/5.01      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3119]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_32,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | ~ v5_orders_2(X1)
% 35.85/5.01      | ~ v2_lattice3(X1)
% 35.85/5.01      | ~ l1_orders_2(X1)
% 35.85/5.01      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f95]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_791,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | ~ v5_orders_2(X1)
% 35.85/5.01      | ~ l1_orders_2(X1)
% 35.85/5.01      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 35.85/5.01      | sK8 != X1 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_32,c_39]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_792,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ v5_orders_2(sK8)
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | k11_lattice3(sK8,X0,X1) = k12_lattice3(sK8,X0,X1) ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_791]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_796,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X0,X1) = k12_lattice3(sK8,X0,X1) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_792,c_41,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3113,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X0_53,X1_53) = k12_lattice3(sK8,X0_53,X1_53) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_796]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3680,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,X1_53) = k12_lattice3(sK8,X0_53,X1_53)
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3113]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_5183,plain,
% 35.85/5.01      ( k11_lattice3(sK8,sK9,X0_53) = k12_lattice3(sK8,sK9,X0_53)
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_3674,c_3680]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_6055,plain,
% 35.85/5.01      ( k11_lattice3(sK8,sK9,sK9) = k12_lattice3(sK8,sK9,sK9) ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_3674,c_5183]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_16,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 35.85/5.01      | ~ l1_orders_2(X1) ),
% 35.85/5.01      inference(cnf_transformation,[],[f79]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1210,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 35.85/5.01      | sK8 != X1 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_16,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1211,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_1210]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3101,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(k11_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_1211]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3692,plain,
% 35.85/5.01      ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(k11_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) = iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3101]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_7921,plain,
% 35.85/5.01      ( m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_6055,c_3692]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_48,plain,
% 35.85/5.01      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_17,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 35.85/5.01      | ~ v5_orders_2(X1)
% 35.85/5.01      | ~ v2_lattice3(X1)
% 35.85/5.01      | ~ l1_orders_2(X1) ),
% 35.85/5.01      inference(cnf_transformation,[],[f80]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_812,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 35.85/5.01      | ~ v5_orders_2(X1)
% 35.85/5.01      | ~ l1_orders_2(X1)
% 35.85/5.01      | sK8 != X1 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_813,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(k12_lattice3(sK8,X0,X1),u1_struct_0(sK8))
% 35.85/5.01      | ~ v5_orders_2(sK8)
% 35.85/5.01      | ~ l1_orders_2(sK8) ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_812]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_817,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(k12_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_813,c_41,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3112,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(k12_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_817]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3179,plain,
% 35.85/5.01      ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(k12_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) = iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3112]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3181,plain,
% 35.85/5.01      ( m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3179]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_8898,plain,
% 35.85/5.01      ( m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) = iProver_top ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_7921,c_48,c_3181]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_33,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | ~ v5_orders_2(X1)
% 35.85/5.01      | ~ l1_orders_2(X1)
% 35.85/5.01      | ~ v1_lattice3(X1)
% 35.85/5.01      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f96]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1121,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | ~ l1_orders_2(X1)
% 35.85/5.01      | ~ v1_lattice3(X1)
% 35.85/5.01      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
% 35.85/5.01      | sK8 != X1 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_33,c_41]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1122,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | ~ v1_lattice3(sK8)
% 35.85/5.01      | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_1121]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1126,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k13_lattice3(sK8,X0,X1) = k10_lattice3(sK8,X0,X1) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_1122,c_40,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3103,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | k13_lattice3(sK8,X0_53,X1_53) = k10_lattice3(sK8,X0_53,X1_53) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_1126]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3690,plain,
% 35.85/5.01      ( k13_lattice3(sK8,X0_53,X1_53) = k10_lattice3(sK8,X0_53,X1_53)
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3103]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_8910,plain,
% 35.85/5.01      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),X0_53) = k10_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),X0_53)
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_8898,c_3690]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_69814,plain,
% 35.85/5.01      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9) = k10_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9) ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_3674,c_8910]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_34,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | ~ v3_orders_2(X1)
% 35.85/5.01      | ~ v5_orders_2(X1)
% 35.85/5.01      | ~ v2_lattice3(X1)
% 35.85/5.01      | ~ l1_orders_2(X1)
% 35.85/5.01      | ~ v1_lattice3(X1)
% 35.85/5.01      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
% 35.85/5.01      inference(cnf_transformation,[],[f97]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_42,negated_conjecture,
% 35.85/5.01      ( v3_orders_2(sK8) ),
% 35.85/5.01      inference(cnf_transformation,[],[f98]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_561,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | ~ v5_orders_2(X1)
% 35.85/5.01      | ~ v2_lattice3(X1)
% 35.85/5.01      | ~ l1_orders_2(X1)
% 35.85/5.01      | ~ v1_lattice3(X1)
% 35.85/5.01      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
% 35.85/5.01      | sK8 != X1 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_34,c_42]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_562,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ v5_orders_2(sK8)
% 35.85/5.01      | ~ v2_lattice3(sK8)
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | ~ v1_lattice3(sK8)
% 35.85/5.01      | k13_lattice3(sK8,k12_lattice3(sK8,X0,X1),X1) = X1 ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_561]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_566,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k13_lattice3(sK8,k12_lattice3(sK8,X0,X1),X1) = X1 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_562,c_41,c_40,c_39,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3118,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | k13_lattice3(sK8,k12_lattice3(sK8,X0_53,X1_53),X1_53) = X1_53 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_566]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3675,plain,
% 35.85/5.01      ( k13_lattice3(sK8,k12_lattice3(sK8,X0_53,X1_53),X1_53) = X1_53
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3118]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_4062,plain,
% 35.85/5.01      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,X0_53),X0_53) = X0_53
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_3674,c_3675]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_4629,plain,
% 35.85/5.01      ( k13_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9) = sK9 ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_3674,c_4062]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_69825,plain,
% 35.85/5.01      ( k10_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9) = sK9 ),
% 35.85/5.01      inference(light_normalisation,[status(thm)],[c_69814,c_4629]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_23,plain,
% 35.85/5.01      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | v2_struct_0(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f107]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_290,plain,
% 35.85/5.01      ( ~ v1_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_23,c_0]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_291,plain,
% 35.85/5.01      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0) ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_290]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1077,plain,
% 35.85/5.01      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_291,c_41]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1078,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8))
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | ~ v1_lattice3(sK8) ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_1077]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1082,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_1078,c_40,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1083,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_1082]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3105,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0_53,k10_lattice3(sK8,X1_53,X0_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,X1_53,X0_53),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_1083]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3688,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0_53,k10_lattice3(sK8,X1_53,X0_53)) = iProver_top
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(k10_lattice3(sK8,X1_53,X0_53),u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3105]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_71243,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK9,k10_lattice3(sK8,k12_lattice3(sK8,sK9,sK9),sK9)) = iProver_top
% 35.85/5.01      | m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_69825,c_3688]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_71246,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK9,sK9) = iProver_top
% 35.85/5.01      | m1_subset_1(k12_lattice3(sK8,sK9,sK9),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(light_normalisation,[status(thm)],[c_71243,c_69825]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_13,plain,
% 35.85/5.01      ( r1_orders_2(X0,X1,sK5(X0,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ sP0(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f69]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3123,plain,
% 35.85/5.01      ( r1_orders_2(X0_52,X0_53,sK5(X0_52,X0_53,X1_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 35.85/5.01      | ~ sP0(X0_52) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_13]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_63821,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ sP0(sK8) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3123]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_63822,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53)) = iProver_top
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | sP0(sK8) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_63821]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_63824,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | sP0(sK8) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_63822]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_20,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | v2_struct_0(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(cnf_transformation,[],[f85]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_309,plain,
% 35.85/5.01      ( ~ v1_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_20,c_0]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_310,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_309]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_982,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | r1_orders_2(X0,X3,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_310,c_41]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_983,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | r1_orders_2(sK8,X2,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | ~ v1_lattice3(sK8)
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_982]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_985,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | r1_orders_2(sK8,X2,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_983,c_40,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_986,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | r1_orders_2(sK8,X2,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_985]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3108,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 35.85/5.01      | r1_orders_2(sK8,X2_53,sK6(sK8,X2_53,X0_53,X1_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_986]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_21308,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | r1_orders_2(sK8,X0_53,sK6(sK8,X0_53,sK10,X1_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK10,X1_53)
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X0_53,sK10) = X1_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3108]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_43138,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0_53,sK6(sK8,X0_53,sK10,sK5(sK8,sK10,X1_53)))
% 35.85/5.01      | ~ r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X1_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X1_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,sK10,X1_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X0_53,sK10) = sK5(sK8,sK10,X1_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_21308]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_43139,plain,
% 35.85/5.01      ( k10_lattice3(sK8,X0_53,sK10) = sK5(sK8,sK10,X1_53)
% 35.85/5.01      | r1_orders_2(sK8,X0_53,sK6(sK8,X0_53,sK10,sK5(sK8,sK10,X1_53))) = iProver_top
% 35.85/5.01      | r1_orders_2(sK8,X0_53,sK5(sK8,sK10,X1_53)) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK5(sK8,sK10,X1_53)) != iProver_top
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,X1_53),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_43138]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_43141,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9)
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) = iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_43139]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_18,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | v2_struct_0(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(cnf_transformation,[],[f87]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_321,plain,
% 35.85/5.01      ( ~ v1_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_18,c_0]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_322,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_321]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_916,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X2,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_322,c_41]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_917,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | ~ v1_lattice3(sK8)
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_916]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_921,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_917,c_40,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_922,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X1,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_921]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3110,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X1_53,sK6(sK8,X2_53,X0_53,X1_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_922]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_11172,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK10,X0_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK10,X0_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,X0_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3110]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_18129,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,sK5(sK8,X0_53,X1_53),sK6(sK8,sK9,sK10,sK5(sK8,X0_53,X1_53)))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK10,sK5(sK8,X0_53,X1_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,sK5(sK8,X0_53,X1_53))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,X0_53,X1_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,X0_53,X1_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_11172]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_25323,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_18129]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_25324,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53)
% 35.85/5.01      | r1_orders_2(sK8,sK5(sK8,sK10,X0_53),sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53)) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_25323]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_25326,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9)
% 35.85/5.01      | r1_orders_2(sK8,sK5(sK8,sK10,sK9),sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_25324]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_19,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | v2_struct_0(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(cnf_transformation,[],[f86]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_316,plain,
% 35.85/5.01      ( ~ v1_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_19,c_0]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_317,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_316]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_949,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | r1_orders_2(X0,X1,sK6(X0,X3,X1,X2))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_317,c_41]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_950,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | ~ v1_lattice3(sK8)
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_949]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_954,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_950,c_40,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_955,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | r1_orders_2(sK8,X0,sK6(sK8,X2,X0,X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_954]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3109,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 35.85/5.01      | r1_orders_2(sK8,X0_53,sK6(sK8,X2_53,X0_53,X1_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_955]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_11173,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,sK10,X0_53)
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,X0_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,X0_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) = X0_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3109]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_18303,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,X0_53,X1_53)))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK10,sK5(sK8,X0_53,X1_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,sK5(sK8,X0_53,X1_53))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,X0_53,X1_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,X0_53,X1_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_11173]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_24902,plain,
% 35.85/5.01      ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_18303]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_24903,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53)
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53))) = iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53)) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_24902]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_24905,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9)
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9))) = iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_24903]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_21,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | v2_struct_0(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(cnf_transformation,[],[f84]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_302,plain,
% 35.85/5.01      ( ~ v1_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_21,c_0]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_303,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_302]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1011,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X3,X2)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | m1_subset_1(sK6(X0,X3,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v1_lattice3(X0)
% 35.85/5.01      | k10_lattice3(X0,X3,X1) = X2
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_303,c_41]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1012,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(sK6(sK8,X2,X0,X1),u1_struct_0(sK8))
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | ~ v1_lattice3(sK8)
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_1011]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1016,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(sK6(sK8,X2,X0,X1),u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_1012,c_40,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1017,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2,X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(sK6(sK8,X2,X0,X1),u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2,X0) = X1 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_1016]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3107,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X2_53,X1_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(sK6(sK8,X2_53,X0_53,X1_53),u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X2_53,X0_53) = X1_53 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_1017]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_4996,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,sK5(sK8,X1_53,X2_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,X3_53,sK5(sK8,X1_53,X2_53))
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X3_53,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(sK6(sK8,X3_53,X0_53,sK5(sK8,X1_53,X2_53)),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,X1_53,X2_53),u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X3_53,X0_53) = sK5(sK8,X1_53,X2_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3107]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_11201,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,sK10,sK5(sK8,X0_53,X1_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,sK5(sK8,X0_53,X1_53))
% 35.85/5.01      | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,X0_53,X1_53)),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,X0_53,X1_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,X0_53,X1_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_4996]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_24115,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53))
% 35.85/5.01      | ~ r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53))
% 35.85/5.01      | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_11201]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_24116,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,X0_53)
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK5(sK8,sK10,X0_53)) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK5(sK8,sK10,X0_53)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,X0_53)),u1_struct_0(sK8)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_24115]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_24118,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) = sK5(sK8,sK10,sK9)
% 35.85/5.01      | r1_orders_2(sK8,sK10,sK5(sK8,sK10,sK9)) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK5(sK8,sK10,sK9)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK6(sK8,sK9,sK10,sK5(sK8,sK10,sK9)),u1_struct_0(sK8)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_24116]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_22666,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3113]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_22668,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_22666]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_22670,plain,
% 35.85/5.01      ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_22668]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_5566,plain,
% 35.85/5.01      ( X0_53 != X1_53
% 35.85/5.01      | X0_53 = k11_lattice3(sK8,X2_53,X3_53)
% 35.85/5.01      | k11_lattice3(sK8,X2_53,X3_53) != X1_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3134]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_17751,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,X1_53) != X2_53
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != X2_53
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,X1_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_5566]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_18461,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,X1_53) != k12_lattice3(sK8,X2_53,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,X1_53)
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,X2_53,k10_lattice3(sK8,sK9,sK10)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_17751]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_22665,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_18461]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_22667,plain,
% 35.85/5.01      ( k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k11_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_22665]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_14,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.85/5.01      | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
% 35.85/5.01      | ~ sP0(X1) ),
% 35.85/5.01      inference(cnf_transformation,[],[f68]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3122,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 35.85/5.01      | m1_subset_1(sK5(X0_52,X1_53,X0_53),u1_struct_0(X0_52))
% 35.85/5.01      | ~ sP0(X0_52) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_14]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_11248,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ sP0(sK8) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3122]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_11249,plain,
% 35.85/5.01      ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | sP0(sK8) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_11248]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_11251,plain,
% 35.85/5.01      ( m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | sP0(sK8) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_11249]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_11250,plain,
% 35.85/5.01      ( m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | ~ sP0(sK8) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_11248]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3136,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,X0_54)
% 35.85/5.01      | m1_subset_1(X1_53,X0_54)
% 35.85/5.01      | X1_53 != X0_53 ),
% 35.85/5.01      theory(equality) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3754,plain,
% 35.85/5.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | m1_subset_1(k10_lattice3(sK8,X1_53,X2_53),u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X1_53,X2_53) != X0_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3136]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_4281,plain,
% 35.85/5.01      ( m1_subset_1(k10_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,X1_53,X2_53),u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,X0_53,X1_53) != sK5(sK8,X1_53,X2_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3754]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_8955,plain,
% 35.85/5.01      ( m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_4281]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_8956,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,X0_53)
% 35.85/5.01      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,X0_53),u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_8955]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_8958,plain,
% 35.85/5.01      ( k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,sK9)
% 35.85/5.01      | m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8)) = iProver_top
% 35.85/5.01      | m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_8956]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_8957,plain,
% 35.85/5.01      ( m1_subset_1(k10_lattice3(sK8,sK9,sK10),u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK5(sK8,sK10,sK9),u1_struct_0(sK8))
% 35.85/5.01      | k10_lattice3(sK8,sK9,sK10) != sK5(sK8,sK10,sK9) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_8955]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_26,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | v2_struct_0(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(cnf_transformation,[],[f93]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_271,plain,
% 35.85/5.01      ( ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_26,c_1]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_272,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_271]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_619,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/5.01      | ~ r1_orders_2(X0,X1,X3)
% 35.85/5.01      | r1_orders_2(X0,sK7(X0,X3,X2,X1),X2)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | k11_lattice3(X0,X3,X2) = X1
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_272,c_39]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_620,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0,X2)
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X2)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ v5_orders_2(sK8)
% 35.85/5.01      | ~ l1_orders_2(sK8)
% 35.85/5.01      | k11_lattice3(sK8,X1,X2) = X0 ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_619]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_624,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0,X1)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0,X2)
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X1,X2,X0),X2)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X1,X2) = X0 ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_620,c_41,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3116,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,X0_53,X2_53)
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X1_53,X2_53,X0_53),X2_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
% 35.85/5.01      | k11_lattice3(sK8,X1_53,X2_53) = X0_53 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_624]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3677,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,X1_53) = X2_53
% 35.85/5.01      | r1_orders_2(sK8,X2_53,X0_53) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,X2_53,X1_53) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X0_53,X1_53,X2_53),X1_53) = iProver_top
% 35.85/5.01      | m1_subset_1(X2_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3116]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3676,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,X1_53) = X2_53
% 35.85/5.01      | r1_orders_2(sK8,X2_53,X0_53) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,X2_53,X1_53) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,sK7(sK8,X0_53,X1_53,X2_53),X2_53) != iProver_top
% 35.85/5.01      | m1_subset_1(X2_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_3117]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_8069,plain,
% 35.85/5.01      ( k11_lattice3(sK8,X0_53,X1_53) = X1_53
% 35.85/5.01      | r1_orders_2(sK8,X1_53,X0_53) != iProver_top
% 35.85/5.01      | r1_orders_2(sK8,X1_53,X1_53) != iProver_top
% 35.85/5.01      | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
% 35.85/5.01      | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(superposition,[status(thm)],[c_3677,c_3676]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_8071,plain,
% 35.85/5.01      ( k11_lattice3(sK8,sK9,sK9) = sK9
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK9) != iProver_top
% 35.85/5.01      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_8069]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3135,plain,
% 35.85/5.01      ( X0_53 != X1_53
% 35.85/5.01      | X2_53 != X3_53
% 35.85/5.01      | k12_lattice3(X0_52,X0_53,X2_53) = k12_lattice3(X0_52,X1_53,X3_53) ),
% 35.85/5.01      theory(equality) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_5165,plain,
% 35.85/5.01      ( k13_lattice3(sK8,sK9,sK10) != X0_53
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X1_53,X0_53)
% 35.85/5.01      | sK9 != X1_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3135]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_7629,plain,
% 35.85/5.01      ( k13_lattice3(sK8,sK9,sK10) != k10_lattice3(sK8,sK9,sK10)
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,X0_53,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | sK9 != X0_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_5165]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_7630,plain,
% 35.85/5.01      ( k13_lattice3(sK8,sK9,sK10) != k10_lattice3(sK8,sK9,sK10)
% 35.85/5.01      | k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) = k12_lattice3(sK8,sK9,k10_lattice3(sK8,sK9,sK10))
% 35.85/5.01      | sK9 != sK9 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_7629]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_5567,plain,
% 35.85/5.01      ( k11_lattice3(sK8,sK9,sK9) != sK9
% 35.85/5.01      | sK9 = k11_lattice3(sK8,sK9,sK9)
% 35.85/5.01      | sK9 != sK9 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_5566]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_5140,plain,
% 35.85/5.01      ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 35.85/5.01      | k13_lattice3(sK8,sK9,sK10) = k10_lattice3(sK8,sK9,sK10) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3103]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3137,plain,
% 35.85/5.01      ( ~ r1_orders_2(X0_52,X0_53,X1_53)
% 35.85/5.01      | r1_orders_2(X0_52,X2_53,X3_53)
% 35.85/5.01      | X2_53 != X0_53
% 35.85/5.01      | X3_53 != X1_53 ),
% 35.85/5.01      theory(equality) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3773,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | r1_orders_2(sK8,X2_53,X3_53)
% 35.85/5.01      | X2_53 != X0_53
% 35.85/5.01      | X3_53 != X1_53 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3137]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3994,plain,
% 35.85/5.01      ( r1_orders_2(sK8,X0_53,X1_53)
% 35.85/5.01      | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_53,X3_53),X3_53)
% 35.85/5.01      | X1_53 != X3_53
% 35.85/5.01      | X0_53 != k11_lattice3(sK8,X2_53,X3_53) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3773]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3996,plain,
% 35.85/5.01      ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK9),sK9)
% 35.85/5.01      | r1_orders_2(sK8,sK9,sK9)
% 35.85/5.01      | sK9 != k11_lattice3(sK8,sK9,sK9)
% 35.85/5.01      | sK9 != sK9 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3994]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_31,plain,
% 35.85/5.01      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | v2_struct_0(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f111]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_238,plain,
% 35.85/5.01      ( ~ l1_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_31,c_1]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_239,plain,
% 35.85/5.01      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ v2_lattice3(X0)
% 35.85/5.01      | ~ l1_orders_2(X0) ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_238]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_771,plain,
% 35.85/5.01      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 35.85/5.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/5.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 35.85/5.01      | ~ v5_orders_2(X0)
% 35.85/5.01      | ~ l1_orders_2(X0)
% 35.85/5.01      | sK8 != X0 ),
% 35.85/5.01      inference(resolution_lifted,[status(thm)],[c_239,c_39]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_772,plain,
% 35.85/5.01      ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
% 35.85/5.01      | ~ v5_orders_2(sK8)
% 35.85/5.01      | ~ l1_orders_2(sK8) ),
% 35.85/5.01      inference(unflattening,[status(thm)],[c_771]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_774,plain,
% 35.85/5.01      ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(global_propositional_subsumption,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_772,c_41,c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_775,plain,
% 35.85/5.01      ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
% 35.85/5.01      inference(renaming,[status(thm)],[c_774]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_1229,plain,
% 35.85/5.01      ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
% 35.85/5.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
% 35.85/5.01      inference(backward_subsumption_resolution,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_1211,c_775]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3099,plain,
% 35.85/5.01      ( r1_orders_2(sK8,k11_lattice3(sK8,X0_53,X1_53),X0_53)
% 35.85/5.01      | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
% 35.85/5.01      | ~ m1_subset_1(X1_53,u1_struct_0(sK8)) ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_1229]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3213,plain,
% 35.85/5.01      ( r1_orders_2(sK8,k11_lattice3(sK8,sK9,sK9),sK9)
% 35.85/5.01      | ~ m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3099]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_35,negated_conjecture,
% 35.85/5.01      ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
% 35.85/5.01      inference(cnf_transformation,[],[f105]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3121,negated_conjecture,
% 35.85/5.01      ( k12_lattice3(sK8,sK9,k13_lattice3(sK8,sK9,sK10)) != sK9 ),
% 35.85/5.01      inference(subtyping,[status(esa)],[c_35]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3133,plain,( X0_53 = X0_53 ),theory(equality) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_3144,plain,
% 35.85/5.01      ( sK9 = sK9 ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_3133]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_4,plain,
% 35.85/5.01      ( ~ sP1(X0) | sP0(X0) | ~ v1_lattice3(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f66]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_130,plain,
% 35.85/5.01      ( sP1(X0) != iProver_top
% 35.85/5.01      | sP0(X0) = iProver_top
% 35.85/5.01      | v1_lattice3(X0) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_132,plain,
% 35.85/5.01      ( sP1(sK8) != iProver_top
% 35.85/5.01      | sP0(sK8) = iProver_top
% 35.85/5.01      | v1_lattice3(sK8) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_130]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_131,plain,
% 35.85/5.01      ( ~ sP1(sK8) | sP0(sK8) | ~ v1_lattice3(sK8) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_4]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_15,plain,
% 35.85/5.01      ( sP1(X0) | ~ l1_orders_2(X0) ),
% 35.85/5.01      inference(cnf_transformation,[],[f78]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_99,plain,
% 35.85/5.01      ( sP1(X0) = iProver_top | l1_orders_2(X0) != iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_101,plain,
% 35.85/5.01      ( sP1(sK8) = iProver_top | l1_orders_2(sK8) != iProver_top ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_99]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_100,plain,
% 35.85/5.01      ( sP1(sK8) | ~ l1_orders_2(sK8) ),
% 35.85/5.01      inference(instantiation,[status(thm)],[c_15]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_36,negated_conjecture,
% 35.85/5.01      ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
% 35.85/5.01      inference(cnf_transformation,[],[f104]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_49,plain,
% 35.85/5.01      ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_47,plain,
% 35.85/5.01      ( l1_orders_2(sK8) = iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(c_45,plain,
% 35.85/5.01      ( v1_lattice3(sK8) = iProver_top ),
% 35.85/5.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 35.85/5.01  
% 35.85/5.01  cnf(contradiction,plain,
% 35.85/5.01      ( $false ),
% 35.85/5.01      inference(minisat,
% 35.85/5.01                [status(thm)],
% 35.85/5.01                [c_107877,c_107869,c_96754,c_95307,c_95216,c_94080,
% 35.85/5.01                 c_73187,c_71246,c_63824,c_43141,c_25326,c_24905,c_24118,
% 35.85/5.01                 c_22670,c_22667,c_11251,c_11250,c_8958,c_8957,c_8071,
% 35.85/5.01                 c_7630,c_5567,c_5140,c_3996,c_3213,c_3181,c_3121,c_3144,
% 35.85/5.01                 c_132,c_131,c_101,c_100,c_49,c_36,c_48,c_37,c_47,c_38,
% 35.85/5.01                 c_45,c_40]) ).
% 35.85/5.01  
% 35.85/5.01  
% 35.85/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.85/5.01  
% 35.85/5.01  ------                               Statistics
% 35.85/5.01  
% 35.85/5.01  ------ General
% 35.85/5.01  
% 35.85/5.01  abstr_ref_over_cycles:                  0
% 35.85/5.01  abstr_ref_under_cycles:                 0
% 35.85/5.01  gc_basic_clause_elim:                   0
% 35.85/5.01  forced_gc_time:                         0
% 35.85/5.01  parsing_time:                           0.015
% 35.85/5.01  unif_index_cands_time:                  0.
% 35.85/5.01  unif_index_add_time:                    0.
% 35.85/5.01  orderings_time:                         0.
% 35.85/5.01  out_proof_time:                         0.028
% 35.85/5.01  total_time:                             4.499
% 35.85/5.01  num_of_symbols:                         55
% 35.85/5.01  num_of_terms:                           182124
% 35.85/5.01  
% 35.85/5.01  ------ Preprocessing
% 35.85/5.01  
% 35.85/5.01  num_of_splits:                          0
% 35.85/5.01  num_of_split_atoms:                     0
% 35.85/5.01  num_of_reused_defs:                     0
% 35.85/5.01  num_eq_ax_congr_red:                    69
% 35.85/5.01  num_of_sem_filtered_clauses:            3
% 35.85/5.01  num_of_subtypes:                        3
% 35.85/5.01  monotx_restored_types:                  0
% 35.85/5.01  sat_num_of_epr_types:                   0
% 35.85/5.01  sat_num_of_non_cyclic_types:            0
% 35.85/5.01  sat_guarded_non_collapsed_types:        1
% 35.85/5.01  num_pure_diseq_elim:                    0
% 35.85/5.01  simp_replaced_by:                       0
% 35.85/5.01  res_preprocessed:                       158
% 35.85/5.01  prep_upred:                             0
% 35.85/5.01  prep_unflattend:                        41
% 35.85/5.01  smt_new_axioms:                         0
% 35.85/5.01  pred_elim_cands:                        3
% 35.85/5.01  pred_elim:                              6
% 35.85/5.01  pred_elim_cl:                           7
% 35.85/5.01  pred_elim_cycles:                       8
% 35.85/5.01  merged_defs:                            0
% 35.85/5.01  merged_defs_ncl:                        0
% 35.85/5.01  bin_hyper_res:                          0
% 35.85/5.01  prep_cycles:                            4
% 35.85/5.01  pred_elim_time:                         0.051
% 35.85/5.01  splitting_time:                         0.
% 35.85/5.01  sem_filter_time:                        0.
% 35.85/5.01  monotx_time:                            0.
% 35.85/5.01  subtype_inf_time:                       0.
% 35.85/5.01  
% 35.85/5.01  ------ Problem properties
% 35.85/5.01  
% 35.85/5.01  clauses:                                34
% 35.85/5.01  conjectures:                            3
% 35.85/5.01  epr:                                    1
% 35.85/5.01  horn:                                   23
% 35.85/5.01  ground:                                 4
% 35.85/5.01  unary:                                  4
% 35.85/5.01  binary:                                 2
% 35.85/5.01  lits:                                   148
% 35.85/5.01  lits_eq:                                13
% 35.85/5.01  fd_pure:                                0
% 35.85/5.01  fd_pseudo:                              0
% 35.85/5.01  fd_cond:                                0
% 35.85/5.01  fd_pseudo_cond:                         8
% 35.85/5.01  ac_symbols:                             0
% 35.85/5.01  
% 35.85/5.01  ------ Propositional Solver
% 35.85/5.01  
% 35.85/5.01  prop_solver_calls:                      42
% 35.85/5.01  prop_fast_solver_calls:                 3763
% 35.85/5.01  smt_solver_calls:                       0
% 35.85/5.01  smt_fast_solver_calls:                  0
% 35.85/5.01  prop_num_of_clauses:                    41034
% 35.85/5.01  prop_preprocess_simplified:             82571
% 35.85/5.01  prop_fo_subsumed:                       122
% 35.85/5.01  prop_solver_time:                       0.
% 35.85/5.01  smt_solver_time:                        0.
% 35.85/5.01  smt_fast_solver_time:                   0.
% 35.85/5.01  prop_fast_solver_time:                  0.
% 35.85/5.01  prop_unsat_core_time:                   0.006
% 35.85/5.01  
% 35.85/5.01  ------ QBF
% 35.85/5.01  
% 35.85/5.01  qbf_q_res:                              0
% 35.85/5.01  qbf_num_tautologies:                    0
% 35.85/5.01  qbf_prep_cycles:                        0
% 35.85/5.01  
% 35.85/5.01  ------ BMC1
% 35.85/5.01  
% 35.85/5.01  bmc1_current_bound:                     -1
% 35.85/5.01  bmc1_last_solved_bound:                 -1
% 35.85/5.01  bmc1_unsat_core_size:                   -1
% 35.85/5.01  bmc1_unsat_core_parents_size:           -1
% 35.85/5.01  bmc1_merge_next_fun:                    0
% 35.85/5.01  bmc1_unsat_core_clauses_time:           0.
% 35.85/5.01  
% 35.85/5.01  ------ Instantiation
% 35.85/5.01  
% 35.85/5.01  inst_num_of_clauses:                    1861
% 35.85/5.01  inst_num_in_passive:                    502
% 35.85/5.01  inst_num_in_active:                     2861
% 35.85/5.01  inst_num_in_unprocessed:                775
% 35.85/5.01  inst_num_of_loops:                      3704
% 35.85/5.01  inst_num_of_learning_restarts:          1
% 35.85/5.01  inst_num_moves_active_passive:          837
% 35.85/5.01  inst_lit_activity:                      0
% 35.85/5.01  inst_lit_activity_moves:                2
% 35.85/5.01  inst_num_tautologies:                   0
% 35.85/5.01  inst_num_prop_implied:                  0
% 35.85/5.01  inst_num_existing_simplified:           0
% 35.85/5.01  inst_num_eq_res_simplified:             0
% 35.85/5.01  inst_num_child_elim:                    0
% 35.85/5.01  inst_num_of_dismatching_blockings:      15109
% 35.85/5.01  inst_num_of_non_proper_insts:           9508
% 35.85/5.01  inst_num_of_duplicates:                 0
% 35.85/5.01  inst_inst_num_from_inst_to_res:         0
% 35.85/5.01  inst_dismatching_checking_time:         0.
% 35.85/5.01  
% 35.85/5.01  ------ Resolution
% 35.85/5.01  
% 35.85/5.01  res_num_of_clauses:                     40
% 35.85/5.01  res_num_in_passive:                     40
% 35.85/5.01  res_num_in_active:                      0
% 35.85/5.01  res_num_of_loops:                       162
% 35.85/5.01  res_forward_subset_subsumed:            77
% 35.85/5.01  res_backward_subset_subsumed:           0
% 35.85/5.01  res_forward_subsumed:                   0
% 35.85/5.01  res_backward_subsumed:                  0
% 35.85/5.01  res_forward_subsumption_resolution:     0
% 35.85/5.01  res_backward_subsumption_resolution:    3
% 35.85/5.01  res_clause_to_clause_subsumption:       21418
% 35.85/5.01  res_orphan_elimination:                 0
% 35.85/5.01  res_tautology_del:                      597
% 35.85/5.01  res_num_eq_res_simplified:              0
% 35.85/5.01  res_num_sel_changes:                    0
% 35.85/5.01  res_moves_from_active_to_pass:          0
% 35.85/5.01  
% 35.85/5.01  ------ Superposition
% 35.85/5.01  
% 35.85/5.01  sup_time_total:                         0.
% 35.85/5.01  sup_time_generating:                    0.
% 35.85/5.01  sup_time_sim_full:                      0.
% 35.85/5.01  sup_time_sim_immed:                     0.
% 35.85/5.01  
% 35.85/5.01  sup_num_of_clauses:                     4053
% 35.85/5.01  sup_num_in_active:                      735
% 35.85/5.01  sup_num_in_passive:                     3318
% 35.85/5.01  sup_num_of_loops:                       740
% 35.85/5.01  sup_fw_superposition:                   3704
% 35.85/5.01  sup_bw_superposition:                   1733
% 35.85/5.01  sup_immediate_simplified:               1308
% 35.85/5.01  sup_given_eliminated:                   0
% 35.85/5.01  comparisons_done:                       0
% 35.85/5.01  comparisons_avoided:                    16
% 35.85/5.01  
% 35.85/5.01  ------ Simplifications
% 35.85/5.01  
% 35.85/5.01  
% 35.85/5.01  sim_fw_subset_subsumed:                 904
% 35.85/5.01  sim_bw_subset_subsumed:                 1
% 35.85/5.01  sim_fw_subsumed:                        105
% 35.85/5.01  sim_bw_subsumed:                        0
% 35.85/5.01  sim_fw_subsumption_res:                 0
% 35.85/5.01  sim_bw_subsumption_res:                 0
% 35.85/5.01  sim_tautology_del:                      5
% 35.85/5.01  sim_eq_tautology_del:                   138
% 35.85/5.01  sim_eq_res_simp:                        0
% 35.85/5.01  sim_fw_demodulated:                     90
% 35.85/5.01  sim_bw_demodulated:                     5
% 35.85/5.01  sim_light_normalised:                   211
% 35.85/5.01  sim_joinable_taut:                      0
% 35.85/5.01  sim_joinable_simp:                      0
% 35.85/5.01  sim_ac_normalised:                      0
% 35.85/5.01  sim_smt_subsumption:                    0
% 35.85/5.01  
%------------------------------------------------------------------------------
