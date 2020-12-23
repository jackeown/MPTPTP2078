%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:06 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 607 expanded)
%              Number of clauses        :   88 ( 153 expanded)
%              Number of leaves         :   15 ( 189 expanded)
%              Depth                    :   20
%              Number of atoms          :  850 (3961 expanded)
%              Number of equality atoms :  154 ( 640 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
              ( k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f38,f37,f36])).

fof(f65,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1087,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1438,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1086,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1439,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X0,X2) = k13_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X0,X2) = k13_lattice3(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_25,c_22])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X1,X0) = k13_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_558])).

cnf(c_1077,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k10_lattice3(sK2,X1_46,X0_46) = k13_lattice3(sK2,X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_559])).

cnf(c_1448,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_1825,plain,
    ( k10_lattice3(sK2,sK3,X0_46) = k13_lattice3(sK2,sK3,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1448])).

cnf(c_1914,plain,
    ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1438,c_1825])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_152,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_1])).

cnf(c_153,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_522,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_24])).

cnf(c_523,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_525,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_25,c_22])).

cnf(c_526,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_525])).

cnf(c_1078,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_526])).

cnf(c_1447,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_3049,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_1447])).

cnf(c_3094,plain,
    ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3049,c_1914])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_542,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_24])).

cnf(c_543,plain,
    ( ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_78,plain,
    ( ~ v1_lattice3(sK2)
    | ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_545,plain,
    ( ~ v2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_24,c_22,c_78])).

cnf(c_765,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_545])).

cnf(c_766,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_23,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_770,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X0,X1)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_766,c_25,c_23,c_22])).

cnf(c_771,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_770])).

cnf(c_1071,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X0_46,X2_46)
    | r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X1_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_771])).

cnf(c_1880,plain,
    ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_46,sK3)
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_1896,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_46,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1880])).

cnf(c_1898,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_10,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_827,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_545])).

cnf(c_828,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_832,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X0,X1)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_25,c_23,c_22])).

cnf(c_833,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_832])).

cnf(c_1069,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X0_46,X2_46)
    | ~ r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_833])).

cnf(c_1882,plain,
    ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_46,sK3)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1888,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_46,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1882])).

cnf(c_1890,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1888])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_575,c_25,c_22])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_579])).

cnf(c_1076,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_580])).

cnf(c_1798,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_1799,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1798])).

cnf(c_1091,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_1785,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
    | sK3 != X0_46
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_1786,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_910,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_911,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_915,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_911,c_25,c_23])).

cnf(c_916,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1,X0) = k11_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_915])).

cnf(c_1068,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1_46,X0_46) = k11_lattice3(sK2,X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_916])).

cnf(c_1727,plain,
    ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_1716,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_1726,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1716])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_316,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_317,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_321,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_24,c_22,c_78])).

cnf(c_1085,plain,
    ( r1_orders_2(sK2,X0_46,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_321])).

cnf(c_1104,plain,
    ( r1_orders_2(sK2,X0_46,X0_46) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_1106,plain,
    ( r1_orders_2(sK2,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_19,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1088,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1090,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1101,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3094,c_1898,c_1890,c_1799,c_1798,c_1786,c_1727,c_1726,c_1106,c_1088,c_1101,c_33,c_20,c_32,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:12:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.19/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/0.98  
% 2.19/0.98  ------  iProver source info
% 2.19/0.98  
% 2.19/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.19/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/0.98  git: non_committed_changes: false
% 2.19/0.98  git: last_make_outside_of_git: false
% 2.19/0.98  
% 2.19/0.98  ------ 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options
% 2.19/0.98  
% 2.19/0.98  --out_options                           all
% 2.19/0.98  --tptp_safe_out                         true
% 2.19/0.98  --problem_path                          ""
% 2.19/0.98  --include_path                          ""
% 2.19/0.98  --clausifier                            res/vclausify_rel
% 2.19/0.98  --clausifier_options                    --mode clausify
% 2.19/0.98  --stdin                                 false
% 2.19/0.98  --stats_out                             all
% 2.19/0.98  
% 2.19/0.98  ------ General Options
% 2.19/0.98  
% 2.19/0.98  --fof                                   false
% 2.19/0.98  --time_out_real                         305.
% 2.19/0.98  --time_out_virtual                      -1.
% 2.19/0.98  --symbol_type_check                     false
% 2.19/0.98  --clausify_out                          false
% 2.19/0.98  --sig_cnt_out                           false
% 2.19/0.98  --trig_cnt_out                          false
% 2.19/0.98  --trig_cnt_out_tolerance                1.
% 2.19/0.98  --trig_cnt_out_sk_spl                   false
% 2.19/0.98  --abstr_cl_out                          false
% 2.19/0.98  
% 2.19/0.98  ------ Global Options
% 2.19/0.98  
% 2.19/0.98  --schedule                              default
% 2.19/0.98  --add_important_lit                     false
% 2.19/0.98  --prop_solver_per_cl                    1000
% 2.19/0.98  --min_unsat_core                        false
% 2.19/0.98  --soft_assumptions                      false
% 2.19/0.98  --soft_lemma_size                       3
% 2.19/0.98  --prop_impl_unit_size                   0
% 2.19/0.98  --prop_impl_unit                        []
% 2.19/0.98  --share_sel_clauses                     true
% 2.19/0.98  --reset_solvers                         false
% 2.19/0.98  --bc_imp_inh                            [conj_cone]
% 2.19/0.98  --conj_cone_tolerance                   3.
% 2.19/0.98  --extra_neg_conj                        none
% 2.19/0.98  --large_theory_mode                     true
% 2.19/0.98  --prolific_symb_bound                   200
% 2.19/0.98  --lt_threshold                          2000
% 2.19/0.98  --clause_weak_htbl                      true
% 2.19/0.98  --gc_record_bc_elim                     false
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing Options
% 2.19/0.98  
% 2.19/0.98  --preprocessing_flag                    true
% 2.19/0.98  --time_out_prep_mult                    0.1
% 2.19/0.98  --splitting_mode                        input
% 2.19/0.98  --splitting_grd                         true
% 2.19/0.98  --splitting_cvd                         false
% 2.19/0.98  --splitting_cvd_svl                     false
% 2.19/0.98  --splitting_nvd                         32
% 2.19/0.98  --sub_typing                            true
% 2.19/0.98  --prep_gs_sim                           true
% 2.19/0.98  --prep_unflatten                        true
% 2.19/0.98  --prep_res_sim                          true
% 2.19/0.98  --prep_upred                            true
% 2.19/0.98  --prep_sem_filter                       exhaustive
% 2.19/0.98  --prep_sem_filter_out                   false
% 2.19/0.98  --pred_elim                             true
% 2.19/0.98  --res_sim_input                         true
% 2.19/0.98  --eq_ax_congr_red                       true
% 2.19/0.98  --pure_diseq_elim                       true
% 2.19/0.98  --brand_transform                       false
% 2.19/0.98  --non_eq_to_eq                          false
% 2.19/0.98  --prep_def_merge                        true
% 2.19/0.98  --prep_def_merge_prop_impl              false
% 2.19/0.98  --prep_def_merge_mbd                    true
% 2.19/0.98  --prep_def_merge_tr_red                 false
% 2.19/0.98  --prep_def_merge_tr_cl                  false
% 2.19/0.98  --smt_preprocessing                     true
% 2.19/0.98  --smt_ac_axioms                         fast
% 2.19/0.98  --preprocessed_out                      false
% 2.19/0.98  --preprocessed_stats                    false
% 2.19/0.98  
% 2.19/0.98  ------ Abstraction refinement Options
% 2.19/0.98  
% 2.19/0.98  --abstr_ref                             []
% 2.19/0.98  --abstr_ref_prep                        false
% 2.19/0.98  --abstr_ref_until_sat                   false
% 2.19/0.98  --abstr_ref_sig_restrict                funpre
% 2.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.98  --abstr_ref_under                       []
% 2.19/0.98  
% 2.19/0.98  ------ SAT Options
% 2.19/0.98  
% 2.19/0.98  --sat_mode                              false
% 2.19/0.98  --sat_fm_restart_options                ""
% 2.19/0.98  --sat_gr_def                            false
% 2.19/0.98  --sat_epr_types                         true
% 2.19/0.98  --sat_non_cyclic_types                  false
% 2.19/0.98  --sat_finite_models                     false
% 2.19/0.98  --sat_fm_lemmas                         false
% 2.19/0.98  --sat_fm_prep                           false
% 2.19/0.98  --sat_fm_uc_incr                        true
% 2.19/0.98  --sat_out_model                         small
% 2.19/0.98  --sat_out_clauses                       false
% 2.19/0.98  
% 2.19/0.98  ------ QBF Options
% 2.19/0.98  
% 2.19/0.98  --qbf_mode                              false
% 2.19/0.98  --qbf_elim_univ                         false
% 2.19/0.98  --qbf_dom_inst                          none
% 2.19/0.98  --qbf_dom_pre_inst                      false
% 2.19/0.98  --qbf_sk_in                             false
% 2.19/0.98  --qbf_pred_elim                         true
% 2.19/0.98  --qbf_split                             512
% 2.19/0.98  
% 2.19/0.98  ------ BMC1 Options
% 2.19/0.98  
% 2.19/0.98  --bmc1_incremental                      false
% 2.19/0.98  --bmc1_axioms                           reachable_all
% 2.19/0.98  --bmc1_min_bound                        0
% 2.19/0.98  --bmc1_max_bound                        -1
% 2.19/0.98  --bmc1_max_bound_default                -1
% 2.19/0.98  --bmc1_symbol_reachability              true
% 2.19/0.98  --bmc1_property_lemmas                  false
% 2.19/0.98  --bmc1_k_induction                      false
% 2.19/0.98  --bmc1_non_equiv_states                 false
% 2.19/0.98  --bmc1_deadlock                         false
% 2.19/0.98  --bmc1_ucm                              false
% 2.19/0.98  --bmc1_add_unsat_core                   none
% 2.19/0.98  --bmc1_unsat_core_children              false
% 2.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.98  --bmc1_out_stat                         full
% 2.19/0.98  --bmc1_ground_init                      false
% 2.19/0.98  --bmc1_pre_inst_next_state              false
% 2.19/0.98  --bmc1_pre_inst_state                   false
% 2.19/0.98  --bmc1_pre_inst_reach_state             false
% 2.19/0.98  --bmc1_out_unsat_core                   false
% 2.19/0.98  --bmc1_aig_witness_out                  false
% 2.19/0.98  --bmc1_verbose                          false
% 2.19/0.98  --bmc1_dump_clauses_tptp                false
% 2.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.98  --bmc1_dump_file                        -
% 2.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.98  --bmc1_ucm_extend_mode                  1
% 2.19/0.98  --bmc1_ucm_init_mode                    2
% 2.19/0.98  --bmc1_ucm_cone_mode                    none
% 2.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.98  --bmc1_ucm_relax_model                  4
% 2.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.98  --bmc1_ucm_layered_model                none
% 2.19/0.98  --bmc1_ucm_max_lemma_size               10
% 2.19/0.98  
% 2.19/0.98  ------ AIG Options
% 2.19/0.98  
% 2.19/0.98  --aig_mode                              false
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation Options
% 2.19/0.98  
% 2.19/0.98  --instantiation_flag                    true
% 2.19/0.98  --inst_sos_flag                         false
% 2.19/0.98  --inst_sos_phase                        true
% 2.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel_side                     num_symb
% 2.19/0.98  --inst_solver_per_active                1400
% 2.19/0.98  --inst_solver_calls_frac                1.
% 2.19/0.98  --inst_passive_queue_type               priority_queues
% 2.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.98  --inst_passive_queues_freq              [25;2]
% 2.19/0.98  --inst_dismatching                      true
% 2.19/0.98  --inst_eager_unprocessed_to_passive     true
% 2.19/0.98  --inst_prop_sim_given                   true
% 2.19/0.98  --inst_prop_sim_new                     false
% 2.19/0.98  --inst_subs_new                         false
% 2.19/0.98  --inst_eq_res_simp                      false
% 2.19/0.98  --inst_subs_given                       false
% 2.19/0.98  --inst_orphan_elimination               true
% 2.19/0.98  --inst_learning_loop_flag               true
% 2.19/0.98  --inst_learning_start                   3000
% 2.19/0.98  --inst_learning_factor                  2
% 2.19/0.98  --inst_start_prop_sim_after_learn       3
% 2.19/0.98  --inst_sel_renew                        solver
% 2.19/0.98  --inst_lit_activity_flag                true
% 2.19/0.98  --inst_restr_to_given                   false
% 2.19/0.98  --inst_activity_threshold               500
% 2.19/0.98  --inst_out_proof                        true
% 2.19/0.98  
% 2.19/0.98  ------ Resolution Options
% 2.19/0.98  
% 2.19/0.98  --resolution_flag                       true
% 2.19/0.98  --res_lit_sel                           adaptive
% 2.19/0.98  --res_lit_sel_side                      none
% 2.19/0.98  --res_ordering                          kbo
% 2.19/0.98  --res_to_prop_solver                    active
% 2.19/0.98  --res_prop_simpl_new                    false
% 2.19/0.98  --res_prop_simpl_given                  true
% 2.19/0.98  --res_passive_queue_type                priority_queues
% 2.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.98  --res_passive_queues_freq               [15;5]
% 2.19/0.98  --res_forward_subs                      full
% 2.19/0.98  --res_backward_subs                     full
% 2.19/0.98  --res_forward_subs_resolution           true
% 2.19/0.98  --res_backward_subs_resolution          true
% 2.19/0.98  --res_orphan_elimination                true
% 2.19/0.98  --res_time_limit                        2.
% 2.19/0.98  --res_out_proof                         true
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Options
% 2.19/0.98  
% 2.19/0.98  --superposition_flag                    true
% 2.19/0.98  --sup_passive_queue_type                priority_queues
% 2.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.98  --demod_completeness_check              fast
% 2.19/0.98  --demod_use_ground                      true
% 2.19/0.98  --sup_to_prop_solver                    passive
% 2.19/0.98  --sup_prop_simpl_new                    true
% 2.19/0.98  --sup_prop_simpl_given                  true
% 2.19/0.98  --sup_fun_splitting                     false
% 2.19/0.98  --sup_smt_interval                      50000
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Simplification Setup
% 2.19/0.98  
% 2.19/0.98  --sup_indices_passive                   []
% 2.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_full_bw                           [BwDemod]
% 2.19/0.98  --sup_immed_triv                        [TrivRules]
% 2.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_immed_bw_main                     []
% 2.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  
% 2.19/0.98  ------ Combination Options
% 2.19/0.98  
% 2.19/0.98  --comb_res_mult                         3
% 2.19/0.98  --comb_sup_mult                         2
% 2.19/0.98  --comb_inst_mult                        10
% 2.19/0.98  
% 2.19/0.98  ------ Debug Options
% 2.19/0.98  
% 2.19/0.98  --dbg_backtrace                         false
% 2.19/0.98  --dbg_dump_prop_clauses                 false
% 2.19/0.98  --dbg_dump_prop_clauses_file            -
% 2.19/0.98  --dbg_out_stat                          false
% 2.19/0.98  ------ Parsing...
% 2.19/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/0.98  ------ Proving...
% 2.19/0.98  ------ Problem Properties 
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  clauses                                 21
% 2.19/0.98  conjectures                             3
% 2.19/0.98  EPR                                     0
% 2.19/0.98  Horn                                    15
% 2.19/0.98  unary                                   3
% 2.19/0.98  binary                                  1
% 2.19/0.98  lits                                    100
% 2.19/0.98  lits eq                                 11
% 2.19/0.98  fd_pure                                 0
% 2.19/0.98  fd_pseudo                               0
% 2.19/0.98  fd_cond                                 0
% 2.19/0.98  fd_pseudo_cond                          8
% 2.19/0.98  AC symbols                              0
% 2.19/0.98  
% 2.19/0.98  ------ Schedule dynamic 5 is on 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  ------ 
% 2.19/0.98  Current options:
% 2.19/0.98  ------ 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options
% 2.19/0.98  
% 2.19/0.98  --out_options                           all
% 2.19/0.98  --tptp_safe_out                         true
% 2.19/0.98  --problem_path                          ""
% 2.19/0.98  --include_path                          ""
% 2.19/0.98  --clausifier                            res/vclausify_rel
% 2.19/0.98  --clausifier_options                    --mode clausify
% 2.19/0.98  --stdin                                 false
% 2.19/0.98  --stats_out                             all
% 2.19/0.98  
% 2.19/0.98  ------ General Options
% 2.19/0.98  
% 2.19/0.98  --fof                                   false
% 2.19/0.98  --time_out_real                         305.
% 2.19/0.98  --time_out_virtual                      -1.
% 2.19/0.98  --symbol_type_check                     false
% 2.19/0.98  --clausify_out                          false
% 2.19/0.98  --sig_cnt_out                           false
% 2.19/0.98  --trig_cnt_out                          false
% 2.19/0.98  --trig_cnt_out_tolerance                1.
% 2.19/0.98  --trig_cnt_out_sk_spl                   false
% 2.19/0.98  --abstr_cl_out                          false
% 2.19/0.98  
% 2.19/0.98  ------ Global Options
% 2.19/0.98  
% 2.19/0.98  --schedule                              default
% 2.19/0.98  --add_important_lit                     false
% 2.19/0.98  --prop_solver_per_cl                    1000
% 2.19/0.98  --min_unsat_core                        false
% 2.19/0.98  --soft_assumptions                      false
% 2.19/0.98  --soft_lemma_size                       3
% 2.19/0.98  --prop_impl_unit_size                   0
% 2.19/0.98  --prop_impl_unit                        []
% 2.19/0.98  --share_sel_clauses                     true
% 2.19/0.98  --reset_solvers                         false
% 2.19/0.98  --bc_imp_inh                            [conj_cone]
% 2.19/0.98  --conj_cone_tolerance                   3.
% 2.19/0.98  --extra_neg_conj                        none
% 2.19/0.98  --large_theory_mode                     true
% 2.19/0.98  --prolific_symb_bound                   200
% 2.19/0.98  --lt_threshold                          2000
% 2.19/0.98  --clause_weak_htbl                      true
% 2.19/0.98  --gc_record_bc_elim                     false
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing Options
% 2.19/0.98  
% 2.19/0.98  --preprocessing_flag                    true
% 2.19/0.98  --time_out_prep_mult                    0.1
% 2.19/0.98  --splitting_mode                        input
% 2.19/0.98  --splitting_grd                         true
% 2.19/0.98  --splitting_cvd                         false
% 2.19/0.98  --splitting_cvd_svl                     false
% 2.19/0.98  --splitting_nvd                         32
% 2.19/0.98  --sub_typing                            true
% 2.19/0.98  --prep_gs_sim                           true
% 2.19/0.98  --prep_unflatten                        true
% 2.19/0.98  --prep_res_sim                          true
% 2.19/0.98  --prep_upred                            true
% 2.19/0.98  --prep_sem_filter                       exhaustive
% 2.19/0.98  --prep_sem_filter_out                   false
% 2.19/0.98  --pred_elim                             true
% 2.19/0.98  --res_sim_input                         true
% 2.19/0.98  --eq_ax_congr_red                       true
% 2.19/0.98  --pure_diseq_elim                       true
% 2.19/0.98  --brand_transform                       false
% 2.19/0.98  --non_eq_to_eq                          false
% 2.19/0.98  --prep_def_merge                        true
% 2.19/0.98  --prep_def_merge_prop_impl              false
% 2.19/0.98  --prep_def_merge_mbd                    true
% 2.19/0.98  --prep_def_merge_tr_red                 false
% 2.19/0.98  --prep_def_merge_tr_cl                  false
% 2.19/0.98  --smt_preprocessing                     true
% 2.19/0.98  --smt_ac_axioms                         fast
% 2.19/0.98  --preprocessed_out                      false
% 2.19/0.98  --preprocessed_stats                    false
% 2.19/0.98  
% 2.19/0.98  ------ Abstraction refinement Options
% 2.19/0.98  
% 2.19/0.98  --abstr_ref                             []
% 2.19/0.98  --abstr_ref_prep                        false
% 2.19/0.98  --abstr_ref_until_sat                   false
% 2.19/0.98  --abstr_ref_sig_restrict                funpre
% 2.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.98  --abstr_ref_under                       []
% 2.19/0.98  
% 2.19/0.98  ------ SAT Options
% 2.19/0.98  
% 2.19/0.98  --sat_mode                              false
% 2.19/0.98  --sat_fm_restart_options                ""
% 2.19/0.98  --sat_gr_def                            false
% 2.19/0.98  --sat_epr_types                         true
% 2.19/0.98  --sat_non_cyclic_types                  false
% 2.19/0.98  --sat_finite_models                     false
% 2.19/0.98  --sat_fm_lemmas                         false
% 2.19/0.98  --sat_fm_prep                           false
% 2.19/0.98  --sat_fm_uc_incr                        true
% 2.19/0.98  --sat_out_model                         small
% 2.19/0.98  --sat_out_clauses                       false
% 2.19/0.98  
% 2.19/0.98  ------ QBF Options
% 2.19/0.98  
% 2.19/0.98  --qbf_mode                              false
% 2.19/0.98  --qbf_elim_univ                         false
% 2.19/0.98  --qbf_dom_inst                          none
% 2.19/0.98  --qbf_dom_pre_inst                      false
% 2.19/0.98  --qbf_sk_in                             false
% 2.19/0.98  --qbf_pred_elim                         true
% 2.19/0.98  --qbf_split                             512
% 2.19/0.98  
% 2.19/0.98  ------ BMC1 Options
% 2.19/0.98  
% 2.19/0.98  --bmc1_incremental                      false
% 2.19/0.98  --bmc1_axioms                           reachable_all
% 2.19/0.98  --bmc1_min_bound                        0
% 2.19/0.98  --bmc1_max_bound                        -1
% 2.19/0.98  --bmc1_max_bound_default                -1
% 2.19/0.98  --bmc1_symbol_reachability              true
% 2.19/0.98  --bmc1_property_lemmas                  false
% 2.19/0.98  --bmc1_k_induction                      false
% 2.19/0.98  --bmc1_non_equiv_states                 false
% 2.19/0.98  --bmc1_deadlock                         false
% 2.19/0.98  --bmc1_ucm                              false
% 2.19/0.98  --bmc1_add_unsat_core                   none
% 2.19/0.98  --bmc1_unsat_core_children              false
% 2.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.98  --bmc1_out_stat                         full
% 2.19/0.98  --bmc1_ground_init                      false
% 2.19/0.98  --bmc1_pre_inst_next_state              false
% 2.19/0.98  --bmc1_pre_inst_state                   false
% 2.19/0.98  --bmc1_pre_inst_reach_state             false
% 2.19/0.98  --bmc1_out_unsat_core                   false
% 2.19/0.98  --bmc1_aig_witness_out                  false
% 2.19/0.98  --bmc1_verbose                          false
% 2.19/0.98  --bmc1_dump_clauses_tptp                false
% 2.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.98  --bmc1_dump_file                        -
% 2.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.98  --bmc1_ucm_extend_mode                  1
% 2.19/0.98  --bmc1_ucm_init_mode                    2
% 2.19/0.98  --bmc1_ucm_cone_mode                    none
% 2.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.98  --bmc1_ucm_relax_model                  4
% 2.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.98  --bmc1_ucm_layered_model                none
% 2.19/0.98  --bmc1_ucm_max_lemma_size               10
% 2.19/0.98  
% 2.19/0.98  ------ AIG Options
% 2.19/0.98  
% 2.19/0.98  --aig_mode                              false
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation Options
% 2.19/0.98  
% 2.19/0.98  --instantiation_flag                    true
% 2.19/0.98  --inst_sos_flag                         false
% 2.19/0.98  --inst_sos_phase                        true
% 2.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel_side                     none
% 2.19/0.98  --inst_solver_per_active                1400
% 2.19/0.98  --inst_solver_calls_frac                1.
% 2.19/0.98  --inst_passive_queue_type               priority_queues
% 2.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.98  --inst_passive_queues_freq              [25;2]
% 2.19/0.98  --inst_dismatching                      true
% 2.19/0.98  --inst_eager_unprocessed_to_passive     true
% 2.19/0.98  --inst_prop_sim_given                   true
% 2.19/0.98  --inst_prop_sim_new                     false
% 2.19/0.98  --inst_subs_new                         false
% 2.19/0.98  --inst_eq_res_simp                      false
% 2.19/0.98  --inst_subs_given                       false
% 2.19/0.98  --inst_orphan_elimination               true
% 2.19/0.98  --inst_learning_loop_flag               true
% 2.19/0.98  --inst_learning_start                   3000
% 2.19/0.98  --inst_learning_factor                  2
% 2.19/0.98  --inst_start_prop_sim_after_learn       3
% 2.19/0.98  --inst_sel_renew                        solver
% 2.19/0.98  --inst_lit_activity_flag                true
% 2.19/0.98  --inst_restr_to_given                   false
% 2.19/0.98  --inst_activity_threshold               500
% 2.19/0.98  --inst_out_proof                        true
% 2.19/0.98  
% 2.19/0.98  ------ Resolution Options
% 2.19/0.98  
% 2.19/0.98  --resolution_flag                       false
% 2.19/0.98  --res_lit_sel                           adaptive
% 2.19/0.98  --res_lit_sel_side                      none
% 2.19/0.98  --res_ordering                          kbo
% 2.19/0.98  --res_to_prop_solver                    active
% 2.19/0.98  --res_prop_simpl_new                    false
% 2.19/0.98  --res_prop_simpl_given                  true
% 2.19/0.98  --res_passive_queue_type                priority_queues
% 2.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.98  --res_passive_queues_freq               [15;5]
% 2.19/0.98  --res_forward_subs                      full
% 2.19/0.98  --res_backward_subs                     full
% 2.19/0.98  --res_forward_subs_resolution           true
% 2.19/0.98  --res_backward_subs_resolution          true
% 2.19/0.98  --res_orphan_elimination                true
% 2.19/0.98  --res_time_limit                        2.
% 2.19/0.98  --res_out_proof                         true
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Options
% 2.19/0.98  
% 2.19/0.98  --superposition_flag                    true
% 2.19/0.98  --sup_passive_queue_type                priority_queues
% 2.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.98  --demod_completeness_check              fast
% 2.19/0.98  --demod_use_ground                      true
% 2.19/0.98  --sup_to_prop_solver                    passive
% 2.19/0.98  --sup_prop_simpl_new                    true
% 2.19/0.98  --sup_prop_simpl_given                  true
% 2.19/0.98  --sup_fun_splitting                     false
% 2.19/0.98  --sup_smt_interval                      50000
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Simplification Setup
% 2.19/0.98  
% 2.19/0.98  --sup_indices_passive                   []
% 2.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_full_bw                           [BwDemod]
% 2.19/0.98  --sup_immed_triv                        [TrivRules]
% 2.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_immed_bw_main                     []
% 2.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  
% 2.19/0.98  ------ Combination Options
% 2.19/0.98  
% 2.19/0.98  --comb_res_mult                         3
% 2.19/0.98  --comb_sup_mult                         2
% 2.19/0.98  --comb_inst_mult                        10
% 2.19/0.98  
% 2.19/0.98  ------ Debug Options
% 2.19/0.98  
% 2.19/0.98  --dbg_backtrace                         false
% 2.19/0.98  --dbg_dump_prop_clauses                 false
% 2.19/0.98  --dbg_dump_prop_clauses_file            -
% 2.19/0.98  --dbg_out_stat                          false
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  ------ Proving...
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  % SZS status Theorem for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  fof(f8,conjecture,(
% 2.19/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f9,negated_conjecture,(
% 2.19/0.98    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 2.19/0.98    inference(negated_conjecture,[],[f8])).
% 2.19/0.98  
% 2.19/0.98  fof(f24,plain,(
% 2.19/0.98    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f9])).
% 2.19/0.98  
% 2.19/0.98  fof(f25,plain,(
% 2.19/0.98    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 2.19/0.98    inference(flattening,[],[f24])).
% 2.19/0.98  
% 2.19/0.98  fof(f38,plain,(
% 2.19/0.98    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f37,plain,(
% 2.19/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f36,plain,(
% 2.19/0.98    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f39,plain,(
% 2.19/0.98    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f38,f37,f36])).
% 2.19/0.98  
% 2.19/0.98  fof(f65,plain,(
% 2.19/0.98    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.19/0.98    inference(cnf_transformation,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  fof(f64,plain,(
% 2.19/0.98    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.19/0.98    inference(cnf_transformation,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  fof(f7,axiom,(
% 2.19/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f22,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f7])).
% 2.19/0.98  
% 2.19/0.98  fof(f23,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.19/0.98    inference(flattening,[],[f22])).
% 2.19/0.98  
% 2.19/0.98  fof(f58,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f23])).
% 2.19/0.98  
% 2.19/0.98  fof(f61,plain,(
% 2.19/0.98    v1_lattice3(sK2)),
% 2.19/0.98    inference(cnf_transformation,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  fof(f60,plain,(
% 2.19/0.98    v5_orders_2(sK2)),
% 2.19/0.98    inference(cnf_transformation,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  fof(f63,plain,(
% 2.19/0.98    l1_orders_2(sK2)),
% 2.19/0.98    inference(cnf_transformation,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  fof(f4,axiom,(
% 2.19/0.98    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f16,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f4])).
% 2.19/0.98  
% 2.19/0.98  fof(f17,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(flattening,[],[f16])).
% 2.19/0.98  
% 2.19/0.98  fof(f26,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(nnf_transformation,[],[f17])).
% 2.19/0.98  
% 2.19/0.98  fof(f27,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(flattening,[],[f26])).
% 2.19/0.98  
% 2.19/0.98  fof(f28,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(rectify,[],[f27])).
% 2.19/0.98  
% 2.19/0.98  fof(f29,plain,(
% 2.19/0.98    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f30,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.19/0.98  
% 2.19/0.98  fof(f43,plain,(
% 2.19/0.98    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f30])).
% 2.19/0.98  
% 2.19/0.98  fof(f69,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.98    inference(equality_resolution,[],[f43])).
% 2.19/0.98  
% 2.19/0.98  fof(f2,axiom,(
% 2.19/0.98    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f12,plain,(
% 2.19/0.98    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.19/0.98    inference(ennf_transformation,[],[f2])).
% 2.19/0.98  
% 2.19/0.98  fof(f13,plain,(
% 2.19/0.98    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.19/0.98    inference(flattening,[],[f12])).
% 2.19/0.98  
% 2.19/0.98  fof(f41,plain,(
% 2.19/0.98    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f13])).
% 2.19/0.98  
% 2.19/0.98  fof(f5,axiom,(
% 2.19/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f18,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f5])).
% 2.19/0.98  
% 2.19/0.98  fof(f19,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(flattening,[],[f18])).
% 2.19/0.98  
% 2.19/0.98  fof(f31,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(nnf_transformation,[],[f19])).
% 2.19/0.98  
% 2.19/0.98  fof(f32,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(flattening,[],[f31])).
% 2.19/0.98  
% 2.19/0.98  fof(f33,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(rectify,[],[f32])).
% 2.19/0.98  
% 2.19/0.98  fof(f34,plain,(
% 2.19/0.98    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f35,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 2.19/0.98  
% 2.19/0.98  fof(f54,plain,(
% 2.19/0.98    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f35])).
% 2.19/0.98  
% 2.19/0.98  fof(f62,plain,(
% 2.19/0.98    v2_lattice3(sK2)),
% 2.19/0.98    inference(cnf_transformation,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  fof(f56,plain,(
% 2.19/0.98    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f35])).
% 2.19/0.98  
% 2.19/0.98  fof(f3,axiom,(
% 2.19/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f14,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f3])).
% 2.19/0.98  
% 2.19/0.98  fof(f15,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.19/0.98    inference(flattening,[],[f14])).
% 2.19/0.98  
% 2.19/0.98  fof(f42,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f15])).
% 2.19/0.98  
% 2.19/0.98  fof(f6,axiom,(
% 2.19/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f20,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f6])).
% 2.19/0.98  
% 2.19/0.98  fof(f21,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.19/0.98    inference(flattening,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f57,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f21])).
% 2.19/0.98  
% 2.19/0.98  fof(f1,axiom,(
% 2.19/0.98    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f10,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f1])).
% 2.19/0.98  
% 2.19/0.98  fof(f11,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.98    inference(flattening,[],[f10])).
% 2.19/0.98  
% 2.19/0.98  fof(f40,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f11])).
% 2.19/0.98  
% 2.19/0.98  fof(f59,plain,(
% 2.19/0.98    v3_orders_2(sK2)),
% 2.19/0.98    inference(cnf_transformation,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  fof(f66,plain,(
% 2.19/0.98    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 2.19/0.98    inference(cnf_transformation,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  cnf(c_20,negated_conjecture,
% 2.19/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.19/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1087,negated_conjecture,
% 2.19/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1438,plain,
% 2.19/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1087]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_21,negated_conjecture,
% 2.19/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.19/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1086,negated_conjecture,
% 2.19/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1439,plain,
% 2.19/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1086]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_18,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.19/0.98      | ~ v5_orders_2(X1)
% 2.19/0.98      | ~ v1_lattice3(X1)
% 2.19/0.98      | ~ l1_orders_2(X1)
% 2.19/0.98      | k10_lattice3(X1,X0,X2) = k13_lattice3(X1,X0,X2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_24,negated_conjecture,
% 2.19/0.98      ( v1_lattice3(sK2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_553,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.19/0.98      | ~ v5_orders_2(X1)
% 2.19/0.98      | ~ l1_orders_2(X1)
% 2.19/0.98      | k10_lattice3(X1,X0,X2) = k13_lattice3(X1,X0,X2)
% 2.19/0.98      | sK2 != X1 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_554,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ v5_orders_2(sK2)
% 2.19/0.98      | ~ l1_orders_2(sK2)
% 2.19/0.98      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_553]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_25,negated_conjecture,
% 2.19/0.98      ( v5_orders_2(sK2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_22,negated_conjecture,
% 2.19/0.98      ( l1_orders_2(sK2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_558,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_554,c_25,c_22]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_559,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | k10_lattice3(sK2,X1,X0) = k13_lattice3(sK2,X1,X0) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_558]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1077,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 2.19/0.98      | k10_lattice3(sK2,X1_46,X0_46) = k13_lattice3(sK2,X1_46,X0_46) ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_559]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1448,plain,
% 2.19/0.98      ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
% 2.19/0.98      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1077]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1825,plain,
% 2.19/0.98      ( k10_lattice3(sK2,sK3,X0_46) = k13_lattice3(sK2,sK3,X0_46)
% 2.19/0.98      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1439,c_1448]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1914,plain,
% 2.19/0.98      ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1438,c_1825]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_9,plain,
% 2.19/0.98      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.19/0.98      | ~ v5_orders_2(X0)
% 2.19/0.98      | ~ v1_lattice3(X0)
% 2.19/0.98      | v2_struct_0(X0)
% 2.19/0.98      | ~ l1_orders_2(X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1,plain,
% 2.19/0.98      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_152,plain,
% 2.19/0.98      ( ~ v1_lattice3(X0)
% 2.19/0.98      | ~ v5_orders_2(X0)
% 2.19/0.98      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.19/0.98      | ~ l1_orders_2(X0) ),
% 2.19/0.98      inference(global_propositional_subsumption,[status(thm)],[c_9,c_1]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_153,plain,
% 2.19/0.98      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.19/0.98      | ~ v5_orders_2(X0)
% 2.19/0.98      | ~ v1_lattice3(X0)
% 2.19/0.98      | ~ l1_orders_2(X0) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_152]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_522,plain,
% 2.19/0.98      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.19/0.98      | ~ v5_orders_2(X0)
% 2.19/0.98      | ~ l1_orders_2(X0)
% 2.19/0.98      | sK2 != X0 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_153,c_24]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_523,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 2.19/0.98      | ~ v5_orders_2(sK2)
% 2.19/0.98      | ~ l1_orders_2(sK2) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_522]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_525,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_523,c_25,c_22]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_526,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_525]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1078,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46))
% 2.19/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_526]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1447,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
% 2.19/0.98      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3049,plain,
% 2.19/0.98      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1914,c_1447]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3094,plain,
% 2.19/0.98      ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(light_normalisation,[status(thm)],[c_3049,c_1914]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_12,plain,
% 2.19/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 2.19/0.98      | ~ r1_orders_2(X0,X1,X3)
% 2.19/0.98      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.19/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | ~ v2_lattice3(X0)
% 2.19/0.98      | ~ v5_orders_2(X0)
% 2.19/0.98      | v2_struct_0(X0)
% 2.19/0.98      | ~ l1_orders_2(X0)
% 2.19/0.98      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_542,plain,
% 2.19/0.98      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK2 != X0 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_24]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_543,plain,
% 2.19/0.98      ( ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_542]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_78,plain,
% 2.19/0.98      ( ~ v1_lattice3(sK2) | ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_545,plain,
% 2.19/0.98      ( ~ v2_struct_0(sK2) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_543,c_24,c_22,c_78]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_765,plain,
% 2.19/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 2.19/0.98      | ~ r1_orders_2(X0,X1,X3)
% 2.19/0.98      | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/0.98      | ~ v2_lattice3(X0)
% 2.19/0.98      | ~ v5_orders_2(X0)
% 2.19/0.98      | ~ l1_orders_2(X0)
% 2.19/0.98      | k11_lattice3(X0,X2,X3) = X1
% 2.19/0.98      | sK2 != X0 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_545]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_766,plain,
% 2.19/0.98      ( ~ r1_orders_2(sK2,X0,X1)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0,X2)
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ v2_lattice3(sK2)
% 2.19/0.98      | ~ v5_orders_2(sK2)
% 2.19/0.98      | ~ l1_orders_2(sK2)
% 2.19/0.98      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_765]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_23,negated_conjecture,
% 2.19/0.98      ( v2_lattice3(sK2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_770,plain,
% 2.19/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0,X2)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0,X1)
% 2.19/0.98      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_766,c_25,c_23,c_22]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_771,plain,
% 2.19/0.98      ( ~ r1_orders_2(sK2,X0,X1)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0,X2)
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.19/0.98      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_770]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1071,plain,
% 2.19/0.98      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0_46,X2_46)
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X1_46)
% 2.19/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 2.19/0.98      | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_771]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1880,plain,
% 2.19/0.98      ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
% 2.19/0.98      | ~ r1_orders_2(sK2,X0_46,sK3)
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3)
% 2.19/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.19/0.98      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1071]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1896,plain,
% 2.19/0.98      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 2.19/0.98      | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 2.19/0.98      | r1_orders_2(sK2,X0_46,sK3) != iProver_top
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3) = iProver_top
% 2.19/0.98      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1880]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1898,plain,
% 2.19/0.98      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
% 2.19/0.98      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 2.19/0.98      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1896]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_10,plain,
% 2.19/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 2.19/0.98      | ~ r1_orders_2(X0,X1,X3)
% 2.19/0.98      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.19/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | ~ v2_lattice3(X0)
% 2.19/0.98      | ~ v5_orders_2(X0)
% 2.19/0.98      | v2_struct_0(X0)
% 2.19/0.98      | ~ l1_orders_2(X0)
% 2.19/0.98      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_827,plain,
% 2.19/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 2.19/0.98      | ~ r1_orders_2(X0,X1,X3)
% 2.19/0.98      | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/0.98      | ~ v2_lattice3(X0)
% 2.19/0.98      | ~ v5_orders_2(X0)
% 2.19/0.98      | ~ l1_orders_2(X0)
% 2.19/0.98      | k11_lattice3(X0,X2,X3) = X1
% 2.19/0.98      | sK2 != X0 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_545]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_828,plain,
% 2.19/0.98      ( ~ r1_orders_2(sK2,X0,X1)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0,X2)
% 2.19/0.98      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ v2_lattice3(sK2)
% 2.19/0.98      | ~ v5_orders_2(sK2)
% 2.19/0.98      | ~ l1_orders_2(sK2)
% 2.19/0.98      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_827]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_832,plain,
% 2.19/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0,X2)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0,X1)
% 2.19/0.98      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_828,c_25,c_23,c_22]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_833,plain,
% 2.19/0.98      ( ~ r1_orders_2(sK2,X0,X1)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0,X2)
% 2.19/0.98      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.19/0.98      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_832]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1069,plain,
% 2.19/0.98      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 2.19/0.98      | ~ r1_orders_2(sK2,X0_46,X2_46)
% 2.19/0.98      | ~ r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X0_46)
% 2.19/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 2.19/0.98      | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_833]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1882,plain,
% 2.19/0.98      ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
% 2.19/0.98      | ~ r1_orders_2(sK2,X0_46,sK3)
% 2.19/0.98      | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46)
% 2.19/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.19/0.98      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1069]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1888,plain,
% 2.19/0.98      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 2.19/0.98      | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 2.19/0.98      | r1_orders_2(sK2,X0_46,sK3) != iProver_top
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46) != iProver_top
% 2.19/0.98      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1882]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1890,plain,
% 2.19/0.98      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.19/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
% 2.19/0.98      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 2.19/0.98      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1888]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.19/0.98      | m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1))
% 2.19/0.98      | ~ v5_orders_2(X1)
% 2.19/0.98      | ~ v1_lattice3(X1)
% 2.19/0.98      | ~ l1_orders_2(X1) ),
% 2.19/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_574,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.19/0.98      | m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1))
% 2.19/0.98      | ~ v5_orders_2(X1)
% 2.19/0.98      | ~ l1_orders_2(X1)
% 2.19/0.98      | sK2 != X1 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_575,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 2.19/0.98      | ~ v5_orders_2(sK2)
% 2.19/0.98      | ~ l1_orders_2(sK2) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_574]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_579,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_575,c_25,c_22]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_580,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_579]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1076,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 2.19/0.98      | m1_subset_1(k13_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_580]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1798,plain,
% 2.19/0.98      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1076]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1799,plain,
% 2.19/0.98      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 2.19/0.98      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1798]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1091,plain,
% 2.19/0.98      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.19/0.98      theory(equality) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1785,plain,
% 2.19/0.98      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
% 2.19/0.98      | sK3 != X0_46
% 2.19/0.98      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1091]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1786,plain,
% 2.19/0.98      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
% 2.19/0.98      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 2.19/0.98      | sK3 != sK3 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1785]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_17,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.19/0.98      | ~ v2_lattice3(X1)
% 2.19/0.98      | ~ v5_orders_2(X1)
% 2.19/0.98      | ~ l1_orders_2(X1)
% 2.19/0.98      | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_910,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.19/0.98      | ~ v2_lattice3(X1)
% 2.19/0.98      | ~ v5_orders_2(X1)
% 2.19/0.98      | k12_lattice3(X1,X0,X2) = k11_lattice3(X1,X0,X2)
% 2.19/0.98      | sK2 != X1 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_911,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | ~ v2_lattice3(sK2)
% 2.19/0.98      | ~ v5_orders_2(sK2)
% 2.19/0.98      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_910]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_915,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_911,c_25,c_23]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_916,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.19/0.98      | k12_lattice3(sK2,X1,X0) = k11_lattice3(sK2,X1,X0) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_915]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1068,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 2.19/0.98      | k12_lattice3(sK2,X1_46,X0_46) = k11_lattice3(sK2,X1_46,X0_46) ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_916]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1727,plain,
% 2.19/0.98      ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.19/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.19/0.98      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1068]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1716,plain,
% 2.19/0.98      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
% 2.19/0.98      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.19/0.98      | sK3 != X0_46 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1091]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1726,plain,
% 2.19/0.98      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 2.19/0.98      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.19/0.98      | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1716]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_0,plain,
% 2.19/0.98      ( r1_orders_2(X0,X1,X1)
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | v2_struct_0(X0)
% 2.19/0.98      | ~ v3_orders_2(X0)
% 2.19/0.98      | ~ l1_orders_2(X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_26,negated_conjecture,
% 2.19/0.98      ( v3_orders_2(sK2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_316,plain,
% 2.19/0.98      ( r1_orders_2(X0,X1,X1)
% 2.19/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/0.98      | v2_struct_0(X0)
% 2.19/0.98      | ~ l1_orders_2(X0)
% 2.19/0.98      | sK2 != X0 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_317,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0,X0)
% 2.19/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.19/0.98      | v2_struct_0(sK2)
% 2.19/0.98      | ~ l1_orders_2(sK2) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_316]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_321,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_317,c_24,c_22,c_78]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1085,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0_46,X0_46)
% 2.19/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK2)) ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_321]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1104,plain,
% 2.19/0.98      ( r1_orders_2(sK2,X0_46,X0_46) = iProver_top
% 2.19/0.98      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1106,plain,
% 2.19/0.98      ( r1_orders_2(sK2,sK3,sK3) = iProver_top
% 2.19/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1104]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_19,negated_conjecture,
% 2.19/0.98      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.19/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1088,negated_conjecture,
% 2.19/0.98      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.19/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1090,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1101,plain,
% 2.19/0.98      ( sK3 = sK3 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1090]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_33,plain,
% 2.19/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_32,plain,
% 2.19/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(contradiction,plain,
% 2.19/0.98      ( $false ),
% 2.19/0.98      inference(minisat,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_3094,c_1898,c_1890,c_1799,c_1798,c_1786,c_1727,c_1726,
% 2.19/0.98                 c_1106,c_1088,c_1101,c_33,c_20,c_32,c_21]) ).
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  ------                               Statistics
% 2.19/0.98  
% 2.19/0.98  ------ General
% 2.19/0.98  
% 2.19/0.98  abstr_ref_over_cycles:                  0
% 2.19/0.98  abstr_ref_under_cycles:                 0
% 2.19/0.98  gc_basic_clause_elim:                   0
% 2.19/0.98  forced_gc_time:                         0
% 2.19/0.98  parsing_time:                           0.01
% 2.19/0.98  unif_index_cands_time:                  0.
% 2.19/0.98  unif_index_add_time:                    0.
% 2.19/0.98  orderings_time:                         0.
% 2.19/0.98  out_proof_time:                         0.012
% 2.19/0.98  total_time:                             0.144
% 2.19/0.98  num_of_symbols:                         49
% 2.19/0.98  num_of_terms:                           2646
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing
% 2.19/0.98  
% 2.19/0.98  num_of_splits:                          0
% 2.19/0.98  num_of_split_atoms:                     0
% 2.19/0.98  num_of_reused_defs:                     0
% 2.19/0.98  num_eq_ax_congr_red:                    45
% 2.19/0.98  num_of_sem_filtered_clauses:            1
% 2.19/0.98  num_of_subtypes:                        3
% 2.19/0.98  monotx_restored_types:                  0
% 2.19/0.98  sat_num_of_epr_types:                   0
% 2.19/0.98  sat_num_of_non_cyclic_types:            0
% 2.19/0.98  sat_guarded_non_collapsed_types:        1
% 2.19/0.98  num_pure_diseq_elim:                    0
% 2.19/0.98  simp_replaced_by:                       0
% 2.19/0.98  res_preprocessed:                       103
% 2.19/0.98  prep_upred:                             0
% 2.19/0.98  prep_unflattend:                        19
% 2.19/0.98  smt_new_axioms:                         0
% 2.19/0.98  pred_elim_cands:                        2
% 2.19/0.98  pred_elim:                              6
% 2.19/0.98  pred_elim_cl:                           6
% 2.19/0.98  pred_elim_cycles:                       8
% 2.19/0.98  merged_defs:                            0
% 2.19/0.98  merged_defs_ncl:                        0
% 2.19/0.98  bin_hyper_res:                          0
% 2.19/0.98  prep_cycles:                            4
% 2.19/0.98  pred_elim_time:                         0.015
% 2.19/0.98  splitting_time:                         0.
% 2.19/0.98  sem_filter_time:                        0.
% 2.19/0.98  monotx_time:                            0.
% 2.19/0.98  subtype_inf_time:                       0.
% 2.19/0.98  
% 2.19/0.98  ------ Problem properties
% 2.19/0.98  
% 2.19/0.98  clauses:                                21
% 2.19/0.98  conjectures:                            3
% 2.19/0.98  epr:                                    0
% 2.19/0.98  horn:                                   15
% 2.19/0.98  ground:                                 3
% 2.19/0.98  unary:                                  3
% 2.19/0.98  binary:                                 1
% 2.19/0.98  lits:                                   100
% 2.19/0.98  lits_eq:                                11
% 2.19/0.98  fd_pure:                                0
% 2.19/0.98  fd_pseudo:                              0
% 2.19/0.98  fd_cond:                                0
% 2.19/0.98  fd_pseudo_cond:                         8
% 2.19/0.98  ac_symbols:                             0
% 2.19/0.98  
% 2.19/0.98  ------ Propositional Solver
% 2.19/0.98  
% 2.19/0.98  prop_solver_calls:                      27
% 2.19/0.98  prop_fast_solver_calls:                 1384
% 2.19/0.98  smt_solver_calls:                       0
% 2.19/0.98  smt_fast_solver_calls:                  0
% 2.19/0.98  prop_num_of_clauses:                    852
% 2.19/0.98  prop_preprocess_simplified:             3706
% 2.19/0.98  prop_fo_subsumed:                       51
% 2.19/0.98  prop_solver_time:                       0.
% 2.19/0.98  smt_solver_time:                        0.
% 2.19/0.98  smt_fast_solver_time:                   0.
% 2.19/0.98  prop_fast_solver_time:                  0.
% 2.19/0.98  prop_unsat_core_time:                   0.
% 2.19/0.98  
% 2.19/0.98  ------ QBF
% 2.19/0.98  
% 2.19/0.98  qbf_q_res:                              0
% 2.19/0.98  qbf_num_tautologies:                    0
% 2.19/0.98  qbf_prep_cycles:                        0
% 2.19/0.98  
% 2.19/0.98  ------ BMC1
% 2.19/0.98  
% 2.19/0.98  bmc1_current_bound:                     -1
% 2.19/0.98  bmc1_last_solved_bound:                 -1
% 2.19/0.98  bmc1_unsat_core_size:                   -1
% 2.19/0.98  bmc1_unsat_core_parents_size:           -1
% 2.19/0.98  bmc1_merge_next_fun:                    0
% 2.19/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation
% 2.19/0.98  
% 2.19/0.98  inst_num_of_clauses:                    219
% 2.19/0.98  inst_num_in_passive:                    50
% 2.19/0.98  inst_num_in_active:                     144
% 2.19/0.98  inst_num_in_unprocessed:                25
% 2.19/0.98  inst_num_of_loops:                      160
% 2.19/0.98  inst_num_of_learning_restarts:          0
% 2.19/0.98  inst_num_moves_active_passive:          12
% 2.19/0.98  inst_lit_activity:                      0
% 2.19/0.98  inst_lit_activity_moves:                0
% 2.19/0.98  inst_num_tautologies:                   0
% 2.19/0.98  inst_num_prop_implied:                  0
% 2.19/0.98  inst_num_existing_simplified:           0
% 2.19/0.98  inst_num_eq_res_simplified:             0
% 2.19/0.98  inst_num_child_elim:                    0
% 2.19/0.98  inst_num_of_dismatching_blockings:      67
% 2.19/0.98  inst_num_of_non_proper_insts:           223
% 2.19/0.98  inst_num_of_duplicates:                 0
% 2.19/0.98  inst_inst_num_from_inst_to_res:         0
% 2.19/0.98  inst_dismatching_checking_time:         0.
% 2.19/0.98  
% 2.19/0.98  ------ Resolution
% 2.19/0.98  
% 2.19/0.98  res_num_of_clauses:                     0
% 2.19/0.98  res_num_in_passive:                     0
% 2.19/0.98  res_num_in_active:                      0
% 2.19/0.98  res_num_of_loops:                       107
% 2.19/0.98  res_forward_subset_subsumed:            19
% 2.19/0.98  res_backward_subset_subsumed:           0
% 2.19/0.98  res_forward_subsumed:                   0
% 2.19/0.98  res_backward_subsumed:                  0
% 2.19/0.98  res_forward_subsumption_resolution:     0
% 2.19/0.98  res_backward_subsumption_resolution:    0
% 2.19/0.98  res_clause_to_clause_subsumption:       384
% 2.19/0.98  res_orphan_elimination:                 0
% 2.19/0.98  res_tautology_del:                      22
% 2.19/0.98  res_num_eq_res_simplified:              0
% 2.19/0.98  res_num_sel_changes:                    0
% 2.19/0.98  res_moves_from_active_to_pass:          0
% 2.19/0.98  
% 2.19/0.98  ------ Superposition
% 2.19/0.98  
% 2.19/0.98  sup_time_total:                         0.
% 2.19/0.98  sup_time_generating:                    0.
% 2.19/0.98  sup_time_sim_full:                      0.
% 2.19/0.98  sup_time_sim_immed:                     0.
% 2.19/0.98  
% 2.19/0.98  sup_num_of_clauses:                     65
% 2.19/0.98  sup_num_in_active:                      32
% 2.19/0.98  sup_num_in_passive:                     33
% 2.19/0.98  sup_num_of_loops:                       31
% 2.19/0.98  sup_fw_superposition:                   42
% 2.19/0.98  sup_bw_superposition:                   5
% 2.19/0.98  sup_immediate_simplified:               14
% 2.19/0.98  sup_given_eliminated:                   0
% 2.19/0.98  comparisons_done:                       0
% 2.19/0.98  comparisons_avoided:                    0
% 2.19/0.98  
% 2.19/0.98  ------ Simplifications
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  sim_fw_subset_subsumed:                 0
% 2.19/0.98  sim_bw_subset_subsumed:                 0
% 2.19/0.98  sim_fw_subsumed:                        0
% 2.19/0.98  sim_bw_subsumed:                        0
% 2.19/0.98  sim_fw_subsumption_res:                 0
% 2.19/0.98  sim_bw_subsumption_res:                 0
% 2.19/0.98  sim_tautology_del:                      0
% 2.19/0.98  sim_eq_tautology_del:                   0
% 2.19/0.98  sim_eq_res_simp:                        0
% 2.19/0.98  sim_fw_demodulated:                     0
% 2.19/0.98  sim_bw_demodulated:                     0
% 2.19/0.98  sim_light_normalised:                   14
% 2.19/0.98  sim_joinable_taut:                      0
% 2.19/0.98  sim_joinable_simp:                      0
% 2.19/0.98  sim_ac_normalised:                      0
% 2.19/0.98  sim_smt_subsumption:                    0
% 2.19/0.98  
%------------------------------------------------------------------------------
