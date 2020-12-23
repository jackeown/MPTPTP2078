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
% DateTime   : Thu Dec  3 12:19:33 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  145 (1840 expanded)
%              Number of clauses        :   97 ( 402 expanded)
%              Number of leaves         :   12 ( 503 expanded)
%              Depth                    :   22
%              Number of atoms          :  807 (14896 expanded)
%              Number of equality atoms :  139 (2852 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k12_lattice3(X0,X1,X2) = X1
                <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <~> r3_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <~> r3_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) != X1 )
              & ( r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) != X1 )
              & ( r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_orders_2(X0,X1,X2)
            | k12_lattice3(X0,X1,X2) != X1 )
          & ( r3_orders_2(X0,X1,X2)
            | k12_lattice3(X0,X1,X2) = X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r3_orders_2(X0,X1,sK3)
          | k12_lattice3(X0,X1,sK3) != X1 )
        & ( r3_orders_2(X0,X1,sK3)
          | k12_lattice3(X0,X1,sK3) = X1 )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) != X1 )
              & ( r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r3_orders_2(X0,sK2,X2)
              | k12_lattice3(X0,sK2,X2) != sK2 )
            & ( r3_orders_2(X0,sK2,X2)
              | k12_lattice3(X0,sK2,X2) = sK2 )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) = X1 )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(sK1,X1,X2)
                | k12_lattice3(sK1,X1,X2) != X1 )
              & ( r3_orders_2(sK1,X1,X2)
                | k12_lattice3(sK1,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v2_lattice3(sK1)
      & v5_orders_2(sK1)
      & v3_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r3_orders_2(sK1,sK2,sK3)
      | k12_lattice3(sK1,sK2,sK3) != sK2 )
    & ( r3_orders_2(sK1,sK2,sK3)
      | k12_lattice3(sK1,sK2,sK3) = sK2 )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v2_lattice3(sK1)
    & v5_orders_2(sK1)
    & v3_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f31])).

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

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f51,plain,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_819,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1144,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_818,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1145,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_614,c_18,c_17])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k12_lattice3(sK1,X0,X1) = k11_lattice3(sK1,X0,X1) ),
    inference(renaming,[status(thm)],[c_618])).

cnf(c_807,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | k12_lattice3(sK1,X0_43,X1_43) = k11_lattice3(sK1,X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_619])).

cnf(c_1156,plain,
    ( k12_lattice3(sK1,X0_43,X1_43) = k11_lattice3(sK1,X0_43,X1_43)
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_1357,plain,
    ( k12_lattice3(sK1,sK2,X0_43) = k11_lattice3(sK1,sK2,X0_43)
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1156])).

cnf(c_1615,plain,
    ( k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1144,c_1357])).

cnf(c_13,negated_conjecture,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_180,plain,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_19,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_315,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_316,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_49,plain,
    ( ~ v2_lattice3(sK1)
    | ~ v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_318,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_17,c_16,c_49])).

cnf(c_319,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_374,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK2
    | sK3 != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_180,c_319])).

cnf(c_375,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_377,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_15,c_14])).

cnf(c_732,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(prop_impl,[status(thm)],[c_15,c_14,c_375])).

cnf(c_816,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_732])).

cnf(c_1147,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_821,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_830,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_297,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_298,plain,
    ( r1_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_302,plain,
    ( r1_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_17,c_16,c_49])).

cnf(c_817,plain,
    ( r1_orders_2(sK1,X0_43,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_834,plain,
    ( r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_822,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1297,plain,
    ( k12_lattice3(sK1,sK2,sK3) != X0_43
    | k12_lattice3(sK1,sK2,sK3) = sK2
    | sK2 != X0_43 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1333,plain,
    ( k12_lattice3(sK1,sK2,sK3) != k11_lattice3(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2
    | sK2 != k11_lattice3(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_1334,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1344,plain,
    ( k11_lattice3(sK1,sK2,sK3) != X0_43
    | sK2 != X0_43
    | sK2 = k11_lattice3(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1345,plain,
    ( k11_lattice3(sK1,sK2,sK3) != sK2
    | sK2 = k11_lattice3(sK1,sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_134,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_3])).

cnf(c_135,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_474,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_135,c_16])).

cnf(c_475,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_477,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_18,c_17])).

cnf(c_478,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_477])).

cnf(c_812,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | r1_orders_2(sK1,sK0(sK1,X2_43,X1_43,X0_43),X2_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2_43,X1_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_478])).

cnf(c_1389,plain,
    ( ~ r1_orders_2(sK1,X0_43,sK3)
    | ~ r1_orders_2(sK1,X0_43,sK2)
    | r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_43),sK2)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = X0_43 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1396,plain,
    ( r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
    | ~ r1_orders_2(sK1,sK2,sK3)
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_146,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_3])).

cnf(c_147,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_408,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_147,c_16])).

cnf(c_409,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_413,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_18,c_17])).

cnf(c_414,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_413])).

cnf(c_814,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | ~ r1_orders_2(sK1,sK0(sK1,X2_43,X1_43,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2_43,X1_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_1387,plain,
    ( ~ r1_orders_2(sK1,X0_43,sK3)
    | ~ r1_orders_2(sK1,X0_43,sK2)
    | ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = X0_43 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_1404,plain,
    ( ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
    | ~ r1_orders_2(sK1,sK2,sK3)
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_1512,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1147,c_15,c_14,c_830,c_834,c_816,c_1333,c_1334,c_1345,c_1396,c_1404])).

cnf(c_1620,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1615,c_1512])).

cnf(c_9,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_115,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_3])).

cnf(c_116,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_115])).

cnf(c_569,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_116,c_16])).

cnf(c_570,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_574,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_18,c_17])).

cnf(c_575,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_574])).

cnf(c_809,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X1_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_575])).

cnf(c_1154,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X1_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_2125,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1154])).

cnf(c_2137,plain,
    ( r1_orders_2(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2125,c_1620])).

cnf(c_12,negated_conjecture,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_178,plain,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_335,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_336,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_340,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_17,c_16,c_49])).

cnf(c_341,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_388,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) != sK2
    | sK3 != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_341])).

cnf(c_389,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_391,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_15,c_14])).

cnf(c_730,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(prop_impl,[status(thm)],[c_15,c_14,c_389])).

cnf(c_815,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_730])).

cnf(c_837,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK2
    | r1_orders_2(sK1,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2137,c_1512,c_837,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:40:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.89/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.01  
% 1.89/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.89/1.01  
% 1.89/1.01  ------  iProver source info
% 1.89/1.01  
% 1.89/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.89/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.89/1.01  git: non_committed_changes: false
% 1.89/1.01  git: last_make_outside_of_git: false
% 1.89/1.01  
% 1.89/1.01  ------ 
% 1.89/1.01  
% 1.89/1.01  ------ Input Options
% 1.89/1.01  
% 1.89/1.01  --out_options                           all
% 1.89/1.01  --tptp_safe_out                         true
% 1.89/1.01  --problem_path                          ""
% 1.89/1.01  --include_path                          ""
% 1.89/1.01  --clausifier                            res/vclausify_rel
% 1.89/1.01  --clausifier_options                    --mode clausify
% 1.89/1.01  --stdin                                 false
% 1.89/1.01  --stats_out                             all
% 1.89/1.01  
% 1.89/1.01  ------ General Options
% 1.89/1.01  
% 1.89/1.01  --fof                                   false
% 1.89/1.01  --time_out_real                         305.
% 1.89/1.01  --time_out_virtual                      -1.
% 1.89/1.01  --symbol_type_check                     false
% 1.89/1.01  --clausify_out                          false
% 1.89/1.01  --sig_cnt_out                           false
% 1.89/1.01  --trig_cnt_out                          false
% 1.89/1.01  --trig_cnt_out_tolerance                1.
% 1.89/1.01  --trig_cnt_out_sk_spl                   false
% 1.89/1.01  --abstr_cl_out                          false
% 1.89/1.01  
% 1.89/1.01  ------ Global Options
% 1.89/1.01  
% 1.89/1.01  --schedule                              default
% 1.89/1.01  --add_important_lit                     false
% 1.89/1.01  --prop_solver_per_cl                    1000
% 1.89/1.01  --min_unsat_core                        false
% 1.89/1.01  --soft_assumptions                      false
% 1.89/1.01  --soft_lemma_size                       3
% 1.89/1.01  --prop_impl_unit_size                   0
% 1.89/1.01  --prop_impl_unit                        []
% 1.89/1.01  --share_sel_clauses                     true
% 1.89/1.01  --reset_solvers                         false
% 1.89/1.01  --bc_imp_inh                            [conj_cone]
% 1.89/1.01  --conj_cone_tolerance                   3.
% 1.89/1.01  --extra_neg_conj                        none
% 1.89/1.01  --large_theory_mode                     true
% 1.89/1.01  --prolific_symb_bound                   200
% 1.89/1.01  --lt_threshold                          2000
% 1.89/1.01  --clause_weak_htbl                      true
% 1.89/1.01  --gc_record_bc_elim                     false
% 1.89/1.01  
% 1.89/1.01  ------ Preprocessing Options
% 1.89/1.01  
% 1.89/1.01  --preprocessing_flag                    true
% 1.89/1.01  --time_out_prep_mult                    0.1
% 1.89/1.01  --splitting_mode                        input
% 1.89/1.01  --splitting_grd                         true
% 1.89/1.01  --splitting_cvd                         false
% 1.89/1.01  --splitting_cvd_svl                     false
% 1.89/1.01  --splitting_nvd                         32
% 1.89/1.01  --sub_typing                            true
% 1.89/1.01  --prep_gs_sim                           true
% 1.89/1.01  --prep_unflatten                        true
% 1.89/1.01  --prep_res_sim                          true
% 1.89/1.01  --prep_upred                            true
% 1.89/1.01  --prep_sem_filter                       exhaustive
% 1.89/1.01  --prep_sem_filter_out                   false
% 1.89/1.01  --pred_elim                             true
% 1.89/1.01  --res_sim_input                         true
% 1.89/1.01  --eq_ax_congr_red                       true
% 1.89/1.01  --pure_diseq_elim                       true
% 1.89/1.01  --brand_transform                       false
% 1.89/1.01  --non_eq_to_eq                          false
% 1.89/1.01  --prep_def_merge                        true
% 1.89/1.01  --prep_def_merge_prop_impl              false
% 1.89/1.01  --prep_def_merge_mbd                    true
% 1.89/1.01  --prep_def_merge_tr_red                 false
% 1.89/1.01  --prep_def_merge_tr_cl                  false
% 1.89/1.01  --smt_preprocessing                     true
% 1.89/1.01  --smt_ac_axioms                         fast
% 1.89/1.01  --preprocessed_out                      false
% 1.89/1.01  --preprocessed_stats                    false
% 1.89/1.01  
% 1.89/1.01  ------ Abstraction refinement Options
% 1.89/1.01  
% 1.89/1.01  --abstr_ref                             []
% 1.89/1.01  --abstr_ref_prep                        false
% 1.89/1.01  --abstr_ref_until_sat                   false
% 1.89/1.01  --abstr_ref_sig_restrict                funpre
% 1.89/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/1.01  --abstr_ref_under                       []
% 1.89/1.01  
% 1.89/1.01  ------ SAT Options
% 1.89/1.01  
% 1.89/1.01  --sat_mode                              false
% 1.89/1.01  --sat_fm_restart_options                ""
% 1.89/1.01  --sat_gr_def                            false
% 1.89/1.01  --sat_epr_types                         true
% 1.89/1.01  --sat_non_cyclic_types                  false
% 1.89/1.01  --sat_finite_models                     false
% 1.89/1.01  --sat_fm_lemmas                         false
% 1.89/1.01  --sat_fm_prep                           false
% 1.89/1.01  --sat_fm_uc_incr                        true
% 1.89/1.01  --sat_out_model                         small
% 1.89/1.01  --sat_out_clauses                       false
% 1.89/1.01  
% 1.89/1.01  ------ QBF Options
% 1.89/1.01  
% 1.89/1.01  --qbf_mode                              false
% 1.89/1.01  --qbf_elim_univ                         false
% 1.89/1.01  --qbf_dom_inst                          none
% 1.89/1.01  --qbf_dom_pre_inst                      false
% 1.89/1.01  --qbf_sk_in                             false
% 1.89/1.01  --qbf_pred_elim                         true
% 1.89/1.01  --qbf_split                             512
% 1.89/1.01  
% 1.89/1.01  ------ BMC1 Options
% 1.89/1.01  
% 1.89/1.01  --bmc1_incremental                      false
% 1.89/1.01  --bmc1_axioms                           reachable_all
% 1.89/1.01  --bmc1_min_bound                        0
% 1.89/1.01  --bmc1_max_bound                        -1
% 1.89/1.01  --bmc1_max_bound_default                -1
% 1.89/1.01  --bmc1_symbol_reachability              true
% 1.89/1.01  --bmc1_property_lemmas                  false
% 1.89/1.01  --bmc1_k_induction                      false
% 1.89/1.01  --bmc1_non_equiv_states                 false
% 1.89/1.01  --bmc1_deadlock                         false
% 1.89/1.01  --bmc1_ucm                              false
% 1.89/1.01  --bmc1_add_unsat_core                   none
% 1.89/1.01  --bmc1_unsat_core_children              false
% 1.89/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/1.01  --bmc1_out_stat                         full
% 1.89/1.01  --bmc1_ground_init                      false
% 1.89/1.01  --bmc1_pre_inst_next_state              false
% 1.89/1.01  --bmc1_pre_inst_state                   false
% 1.89/1.01  --bmc1_pre_inst_reach_state             false
% 1.89/1.01  --bmc1_out_unsat_core                   false
% 1.89/1.01  --bmc1_aig_witness_out                  false
% 1.89/1.01  --bmc1_verbose                          false
% 1.89/1.01  --bmc1_dump_clauses_tptp                false
% 1.89/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.89/1.01  --bmc1_dump_file                        -
% 1.89/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.89/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.89/1.01  --bmc1_ucm_extend_mode                  1
% 1.89/1.01  --bmc1_ucm_init_mode                    2
% 1.89/1.01  --bmc1_ucm_cone_mode                    none
% 1.89/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.89/1.01  --bmc1_ucm_relax_model                  4
% 1.89/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.89/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/1.01  --bmc1_ucm_layered_model                none
% 1.89/1.01  --bmc1_ucm_max_lemma_size               10
% 1.89/1.01  
% 1.89/1.01  ------ AIG Options
% 1.89/1.01  
% 1.89/1.01  --aig_mode                              false
% 1.89/1.01  
% 1.89/1.01  ------ Instantiation Options
% 1.89/1.01  
% 1.89/1.01  --instantiation_flag                    true
% 1.89/1.01  --inst_sos_flag                         false
% 1.89/1.01  --inst_sos_phase                        true
% 1.89/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/1.01  --inst_lit_sel_side                     num_symb
% 1.89/1.01  --inst_solver_per_active                1400
% 1.89/1.01  --inst_solver_calls_frac                1.
% 1.89/1.01  --inst_passive_queue_type               priority_queues
% 1.89/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/1.01  --inst_passive_queues_freq              [25;2]
% 1.89/1.01  --inst_dismatching                      true
% 1.89/1.01  --inst_eager_unprocessed_to_passive     true
% 1.89/1.01  --inst_prop_sim_given                   true
% 1.89/1.01  --inst_prop_sim_new                     false
% 1.89/1.01  --inst_subs_new                         false
% 1.89/1.01  --inst_eq_res_simp                      false
% 1.89/1.01  --inst_subs_given                       false
% 1.89/1.01  --inst_orphan_elimination               true
% 1.89/1.01  --inst_learning_loop_flag               true
% 1.89/1.01  --inst_learning_start                   3000
% 1.89/1.01  --inst_learning_factor                  2
% 1.89/1.01  --inst_start_prop_sim_after_learn       3
% 1.89/1.01  --inst_sel_renew                        solver
% 1.89/1.01  --inst_lit_activity_flag                true
% 1.89/1.01  --inst_restr_to_given                   false
% 1.89/1.01  --inst_activity_threshold               500
% 1.89/1.01  --inst_out_proof                        true
% 1.89/1.01  
% 1.89/1.01  ------ Resolution Options
% 1.89/1.01  
% 1.89/1.01  --resolution_flag                       true
% 1.89/1.01  --res_lit_sel                           adaptive
% 1.89/1.01  --res_lit_sel_side                      none
% 1.89/1.01  --res_ordering                          kbo
% 1.89/1.01  --res_to_prop_solver                    active
% 1.89/1.01  --res_prop_simpl_new                    false
% 1.89/1.01  --res_prop_simpl_given                  true
% 1.89/1.01  --res_passive_queue_type                priority_queues
% 1.89/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/1.01  --res_passive_queues_freq               [15;5]
% 1.89/1.01  --res_forward_subs                      full
% 1.89/1.01  --res_backward_subs                     full
% 1.89/1.01  --res_forward_subs_resolution           true
% 1.89/1.01  --res_backward_subs_resolution          true
% 1.89/1.01  --res_orphan_elimination                true
% 1.89/1.01  --res_time_limit                        2.
% 1.89/1.01  --res_out_proof                         true
% 1.89/1.01  
% 1.89/1.01  ------ Superposition Options
% 1.89/1.01  
% 1.89/1.01  --superposition_flag                    true
% 1.89/1.01  --sup_passive_queue_type                priority_queues
% 1.89/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.89/1.01  --demod_completeness_check              fast
% 1.89/1.01  --demod_use_ground                      true
% 1.89/1.01  --sup_to_prop_solver                    passive
% 1.89/1.01  --sup_prop_simpl_new                    true
% 1.89/1.01  --sup_prop_simpl_given                  true
% 1.89/1.01  --sup_fun_splitting                     false
% 1.89/1.01  --sup_smt_interval                      50000
% 1.89/1.01  
% 1.89/1.01  ------ Superposition Simplification Setup
% 1.89/1.01  
% 1.89/1.01  --sup_indices_passive                   []
% 1.89/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_full_bw                           [BwDemod]
% 1.89/1.01  --sup_immed_triv                        [TrivRules]
% 1.89/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_immed_bw_main                     []
% 1.89/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.01  
% 1.89/1.01  ------ Combination Options
% 1.89/1.01  
% 1.89/1.01  --comb_res_mult                         3
% 1.89/1.01  --comb_sup_mult                         2
% 1.89/1.01  --comb_inst_mult                        10
% 1.89/1.01  
% 1.89/1.01  ------ Debug Options
% 1.89/1.01  
% 1.89/1.01  --dbg_backtrace                         false
% 1.89/1.01  --dbg_dump_prop_clauses                 false
% 1.89/1.01  --dbg_dump_prop_clauses_file            -
% 1.89/1.01  --dbg_out_stat                          false
% 1.89/1.01  ------ Parsing...
% 1.89/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.89/1.01  
% 1.89/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.89/1.01  
% 1.89/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.89/1.01  
% 1.89/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.89/1.01  ------ Proving...
% 1.89/1.01  ------ Problem Properties 
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  clauses                                 13
% 1.89/1.01  conjectures                             2
% 1.89/1.01  EPR                                     0
% 1.89/1.01  Horn                                    9
% 1.89/1.01  unary                                   2
% 1.89/1.01  binary                                  3
% 1.89/1.01  lits                                    54
% 1.89/1.01  lits eq                                 7
% 1.89/1.01  fd_pure                                 0
% 1.89/1.01  fd_pseudo                               0
% 1.89/1.01  fd_cond                                 0
% 1.89/1.01  fd_pseudo_cond                          4
% 1.89/1.01  AC symbols                              0
% 1.89/1.01  
% 1.89/1.01  ------ Schedule dynamic 5 is on 
% 1.89/1.01  
% 1.89/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  ------ 
% 1.89/1.01  Current options:
% 1.89/1.01  ------ 
% 1.89/1.01  
% 1.89/1.01  ------ Input Options
% 1.89/1.01  
% 1.89/1.01  --out_options                           all
% 1.89/1.01  --tptp_safe_out                         true
% 1.89/1.01  --problem_path                          ""
% 1.89/1.01  --include_path                          ""
% 1.89/1.01  --clausifier                            res/vclausify_rel
% 1.89/1.01  --clausifier_options                    --mode clausify
% 1.89/1.01  --stdin                                 false
% 1.89/1.01  --stats_out                             all
% 1.89/1.01  
% 1.89/1.01  ------ General Options
% 1.89/1.01  
% 1.89/1.01  --fof                                   false
% 1.89/1.01  --time_out_real                         305.
% 1.89/1.01  --time_out_virtual                      -1.
% 1.89/1.01  --symbol_type_check                     false
% 1.89/1.01  --clausify_out                          false
% 1.89/1.01  --sig_cnt_out                           false
% 1.89/1.01  --trig_cnt_out                          false
% 1.89/1.01  --trig_cnt_out_tolerance                1.
% 1.89/1.01  --trig_cnt_out_sk_spl                   false
% 1.89/1.01  --abstr_cl_out                          false
% 1.89/1.01  
% 1.89/1.01  ------ Global Options
% 1.89/1.01  
% 1.89/1.01  --schedule                              default
% 1.89/1.01  --add_important_lit                     false
% 1.89/1.01  --prop_solver_per_cl                    1000
% 1.89/1.01  --min_unsat_core                        false
% 1.89/1.01  --soft_assumptions                      false
% 1.89/1.01  --soft_lemma_size                       3
% 1.89/1.01  --prop_impl_unit_size                   0
% 1.89/1.01  --prop_impl_unit                        []
% 1.89/1.01  --share_sel_clauses                     true
% 1.89/1.01  --reset_solvers                         false
% 1.89/1.01  --bc_imp_inh                            [conj_cone]
% 1.89/1.01  --conj_cone_tolerance                   3.
% 1.89/1.01  --extra_neg_conj                        none
% 1.89/1.01  --large_theory_mode                     true
% 1.89/1.01  --prolific_symb_bound                   200
% 1.89/1.01  --lt_threshold                          2000
% 1.89/1.01  --clause_weak_htbl                      true
% 1.89/1.01  --gc_record_bc_elim                     false
% 1.89/1.01  
% 1.89/1.01  ------ Preprocessing Options
% 1.89/1.01  
% 1.89/1.01  --preprocessing_flag                    true
% 1.89/1.01  --time_out_prep_mult                    0.1
% 1.89/1.01  --splitting_mode                        input
% 1.89/1.01  --splitting_grd                         true
% 1.89/1.01  --splitting_cvd                         false
% 1.89/1.01  --splitting_cvd_svl                     false
% 1.89/1.01  --splitting_nvd                         32
% 1.89/1.01  --sub_typing                            true
% 1.89/1.01  --prep_gs_sim                           true
% 1.89/1.01  --prep_unflatten                        true
% 1.89/1.01  --prep_res_sim                          true
% 1.89/1.01  --prep_upred                            true
% 1.89/1.01  --prep_sem_filter                       exhaustive
% 1.89/1.01  --prep_sem_filter_out                   false
% 1.89/1.01  --pred_elim                             true
% 1.89/1.01  --res_sim_input                         true
% 1.89/1.01  --eq_ax_congr_red                       true
% 1.89/1.01  --pure_diseq_elim                       true
% 1.89/1.01  --brand_transform                       false
% 1.89/1.01  --non_eq_to_eq                          false
% 1.89/1.01  --prep_def_merge                        true
% 1.89/1.01  --prep_def_merge_prop_impl              false
% 1.89/1.01  --prep_def_merge_mbd                    true
% 1.89/1.01  --prep_def_merge_tr_red                 false
% 1.89/1.01  --prep_def_merge_tr_cl                  false
% 1.89/1.01  --smt_preprocessing                     true
% 1.89/1.01  --smt_ac_axioms                         fast
% 1.89/1.01  --preprocessed_out                      false
% 1.89/1.01  --preprocessed_stats                    false
% 1.89/1.01  
% 1.89/1.01  ------ Abstraction refinement Options
% 1.89/1.01  
% 1.89/1.01  --abstr_ref                             []
% 1.89/1.01  --abstr_ref_prep                        false
% 1.89/1.01  --abstr_ref_until_sat                   false
% 1.89/1.01  --abstr_ref_sig_restrict                funpre
% 1.89/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/1.01  --abstr_ref_under                       []
% 1.89/1.01  
% 1.89/1.01  ------ SAT Options
% 1.89/1.01  
% 1.89/1.01  --sat_mode                              false
% 1.89/1.01  --sat_fm_restart_options                ""
% 1.89/1.01  --sat_gr_def                            false
% 1.89/1.01  --sat_epr_types                         true
% 1.89/1.01  --sat_non_cyclic_types                  false
% 1.89/1.01  --sat_finite_models                     false
% 1.89/1.01  --sat_fm_lemmas                         false
% 1.89/1.01  --sat_fm_prep                           false
% 1.89/1.01  --sat_fm_uc_incr                        true
% 1.89/1.01  --sat_out_model                         small
% 1.89/1.01  --sat_out_clauses                       false
% 1.89/1.01  
% 1.89/1.01  ------ QBF Options
% 1.89/1.01  
% 1.89/1.01  --qbf_mode                              false
% 1.89/1.01  --qbf_elim_univ                         false
% 1.89/1.01  --qbf_dom_inst                          none
% 1.89/1.01  --qbf_dom_pre_inst                      false
% 1.89/1.01  --qbf_sk_in                             false
% 1.89/1.01  --qbf_pred_elim                         true
% 1.89/1.01  --qbf_split                             512
% 1.89/1.01  
% 1.89/1.01  ------ BMC1 Options
% 1.89/1.01  
% 1.89/1.01  --bmc1_incremental                      false
% 1.89/1.01  --bmc1_axioms                           reachable_all
% 1.89/1.01  --bmc1_min_bound                        0
% 1.89/1.01  --bmc1_max_bound                        -1
% 1.89/1.01  --bmc1_max_bound_default                -1
% 1.89/1.01  --bmc1_symbol_reachability              true
% 1.89/1.01  --bmc1_property_lemmas                  false
% 1.89/1.01  --bmc1_k_induction                      false
% 1.89/1.01  --bmc1_non_equiv_states                 false
% 1.89/1.01  --bmc1_deadlock                         false
% 1.89/1.01  --bmc1_ucm                              false
% 1.89/1.01  --bmc1_add_unsat_core                   none
% 1.89/1.01  --bmc1_unsat_core_children              false
% 1.89/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/1.01  --bmc1_out_stat                         full
% 1.89/1.01  --bmc1_ground_init                      false
% 1.89/1.01  --bmc1_pre_inst_next_state              false
% 1.89/1.01  --bmc1_pre_inst_state                   false
% 1.89/1.01  --bmc1_pre_inst_reach_state             false
% 1.89/1.01  --bmc1_out_unsat_core                   false
% 1.89/1.01  --bmc1_aig_witness_out                  false
% 1.89/1.01  --bmc1_verbose                          false
% 1.89/1.01  --bmc1_dump_clauses_tptp                false
% 1.89/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.89/1.01  --bmc1_dump_file                        -
% 1.89/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.89/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.89/1.01  --bmc1_ucm_extend_mode                  1
% 1.89/1.01  --bmc1_ucm_init_mode                    2
% 1.89/1.01  --bmc1_ucm_cone_mode                    none
% 1.89/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.89/1.01  --bmc1_ucm_relax_model                  4
% 1.89/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.89/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/1.01  --bmc1_ucm_layered_model                none
% 1.89/1.01  --bmc1_ucm_max_lemma_size               10
% 1.89/1.01  
% 1.89/1.01  ------ AIG Options
% 1.89/1.01  
% 1.89/1.01  --aig_mode                              false
% 1.89/1.01  
% 1.89/1.01  ------ Instantiation Options
% 1.89/1.01  
% 1.89/1.01  --instantiation_flag                    true
% 1.89/1.01  --inst_sos_flag                         false
% 1.89/1.01  --inst_sos_phase                        true
% 1.89/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/1.01  --inst_lit_sel_side                     none
% 1.89/1.01  --inst_solver_per_active                1400
% 1.89/1.01  --inst_solver_calls_frac                1.
% 1.89/1.01  --inst_passive_queue_type               priority_queues
% 1.89/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/1.01  --inst_passive_queues_freq              [25;2]
% 1.89/1.01  --inst_dismatching                      true
% 1.89/1.01  --inst_eager_unprocessed_to_passive     true
% 1.89/1.01  --inst_prop_sim_given                   true
% 1.89/1.01  --inst_prop_sim_new                     false
% 1.89/1.01  --inst_subs_new                         false
% 1.89/1.01  --inst_eq_res_simp                      false
% 1.89/1.01  --inst_subs_given                       false
% 1.89/1.01  --inst_orphan_elimination               true
% 1.89/1.01  --inst_learning_loop_flag               true
% 1.89/1.01  --inst_learning_start                   3000
% 1.89/1.01  --inst_learning_factor                  2
% 1.89/1.01  --inst_start_prop_sim_after_learn       3
% 1.89/1.01  --inst_sel_renew                        solver
% 1.89/1.01  --inst_lit_activity_flag                true
% 1.89/1.01  --inst_restr_to_given                   false
% 1.89/1.01  --inst_activity_threshold               500
% 1.89/1.01  --inst_out_proof                        true
% 1.89/1.01  
% 1.89/1.01  ------ Resolution Options
% 1.89/1.01  
% 1.89/1.01  --resolution_flag                       false
% 1.89/1.01  --res_lit_sel                           adaptive
% 1.89/1.01  --res_lit_sel_side                      none
% 1.89/1.01  --res_ordering                          kbo
% 1.89/1.01  --res_to_prop_solver                    active
% 1.89/1.01  --res_prop_simpl_new                    false
% 1.89/1.01  --res_prop_simpl_given                  true
% 1.89/1.01  --res_passive_queue_type                priority_queues
% 1.89/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/1.01  --res_passive_queues_freq               [15;5]
% 1.89/1.01  --res_forward_subs                      full
% 1.89/1.01  --res_backward_subs                     full
% 1.89/1.01  --res_forward_subs_resolution           true
% 1.89/1.01  --res_backward_subs_resolution          true
% 1.89/1.01  --res_orphan_elimination                true
% 1.89/1.01  --res_time_limit                        2.
% 1.89/1.01  --res_out_proof                         true
% 1.89/1.01  
% 1.89/1.01  ------ Superposition Options
% 1.89/1.01  
% 1.89/1.01  --superposition_flag                    true
% 1.89/1.01  --sup_passive_queue_type                priority_queues
% 1.89/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.89/1.01  --demod_completeness_check              fast
% 1.89/1.01  --demod_use_ground                      true
% 1.89/1.01  --sup_to_prop_solver                    passive
% 1.89/1.01  --sup_prop_simpl_new                    true
% 1.89/1.01  --sup_prop_simpl_given                  true
% 1.89/1.01  --sup_fun_splitting                     false
% 1.89/1.01  --sup_smt_interval                      50000
% 1.89/1.01  
% 1.89/1.01  ------ Superposition Simplification Setup
% 1.89/1.01  
% 1.89/1.01  --sup_indices_passive                   []
% 1.89/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_full_bw                           [BwDemod]
% 1.89/1.01  --sup_immed_triv                        [TrivRules]
% 1.89/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_immed_bw_main                     []
% 1.89/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.01  
% 1.89/1.01  ------ Combination Options
% 1.89/1.01  
% 1.89/1.01  --comb_res_mult                         3
% 1.89/1.01  --comb_sup_mult                         2
% 1.89/1.01  --comb_inst_mult                        10
% 1.89/1.01  
% 1.89/1.01  ------ Debug Options
% 1.89/1.01  
% 1.89/1.01  --dbg_backtrace                         false
% 1.89/1.01  --dbg_dump_prop_clauses                 false
% 1.89/1.01  --dbg_dump_prop_clauses_file            -
% 1.89/1.01  --dbg_out_stat                          false
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  ------ Proving...
% 1.89/1.01  
% 1.89/1.01  
% 1.89/1.01  % SZS status Theorem for theBenchmark.p
% 1.89/1.01  
% 1.89/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.89/1.01  
% 1.89/1.01  fof(f6,conjecture,(
% 1.89/1.01    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 1.89/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f7,negated_conjecture,(
% 1.89/1.01    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 1.89/1.01    inference(negated_conjecture,[],[f6])).
% 1.89/1.01  
% 1.89/1.01  fof(f18,plain,(
% 1.89/1.01    ? [X0] : (? [X1] : (? [X2] : ((k12_lattice3(X0,X1,X2) = X1 <~> r3_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.89/1.01    inference(ennf_transformation,[],[f7])).
% 1.89/1.01  
% 1.89/1.01  fof(f19,plain,(
% 1.89/1.01    ? [X0] : (? [X1] : (? [X2] : ((k12_lattice3(X0,X1,X2) = X1 <~> r3_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.89/1.01    inference(flattening,[],[f18])).
% 1.89/1.01  
% 1.89/1.01  fof(f26,plain,(
% 1.89/1.01    ? [X0] : (? [X1] : (? [X2] : (((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.89/1.01    inference(nnf_transformation,[],[f19])).
% 1.89/1.01  
% 1.89/1.01  fof(f27,plain,(
% 1.89/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.89/1.01    inference(flattening,[],[f26])).
% 1.89/1.01  
% 1.89/1.01  fof(f30,plain,(
% 1.89/1.01    ( ! [X0,X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r3_orders_2(X0,X1,sK3) | k12_lattice3(X0,X1,sK3) != X1) & (r3_orders_2(X0,X1,sK3) | k12_lattice3(X0,X1,sK3) = X1) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.89/1.01    introduced(choice_axiom,[])).
% 1.89/1.01  
% 1.89/1.01  fof(f29,plain,(
% 1.89/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_orders_2(X0,sK2,X2) | k12_lattice3(X0,sK2,X2) != sK2) & (r3_orders_2(X0,sK2,X2) | k12_lattice3(X0,sK2,X2) = sK2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.89/1.01    introduced(choice_axiom,[])).
% 1.89/1.01  
% 1.89/1.01  fof(f28,plain,(
% 1.89/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : ((~r3_orders_2(sK1,X1,X2) | k12_lattice3(sK1,X1,X2) != X1) & (r3_orders_2(sK1,X1,X2) | k12_lattice3(sK1,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v2_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1))),
% 1.89/1.01    introduced(choice_axiom,[])).
% 1.89/1.01  
% 1.89/1.01  fof(f31,plain,(
% 1.89/1.01    (((~r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2) & (r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v2_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1)),
% 1.89/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).
% 1.89/1.01  
% 1.89/1.01  fof(f49,plain,(
% 1.89/1.01    m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f48,plain,(
% 1.89/1.01    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f5,axiom,(
% 1.89/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 1.89/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f16,plain,(
% 1.89/1.01    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.89/1.01    inference(ennf_transformation,[],[f5])).
% 1.89/1.01  
% 1.89/1.01  fof(f17,plain,(
% 1.89/1.01    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 1.89/1.01    inference(flattening,[],[f16])).
% 1.89/1.01  
% 1.89/1.01  fof(f43,plain,(
% 1.89/1.01    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f17])).
% 1.89/1.01  
% 1.89/1.01  fof(f47,plain,(
% 1.89/1.01    l1_orders_2(sK1)),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f45,plain,(
% 1.89/1.01    v5_orders_2(sK1)),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f46,plain,(
% 1.89/1.01    v2_lattice3(sK1)),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f50,plain,(
% 1.89/1.01    r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f1,axiom,(
% 1.89/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.89/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f8,plain,(
% 1.89/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.89/1.01    inference(ennf_transformation,[],[f1])).
% 1.89/1.01  
% 1.89/1.01  fof(f9,plain,(
% 1.89/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.89/1.01    inference(flattening,[],[f8])).
% 1.89/1.01  
% 1.89/1.01  fof(f20,plain,(
% 1.89/1.01    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.89/1.01    inference(nnf_transformation,[],[f9])).
% 1.89/1.01  
% 1.89/1.01  fof(f32,plain,(
% 1.89/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f20])).
% 1.89/1.01  
% 1.89/1.01  fof(f44,plain,(
% 1.89/1.01    v3_orders_2(sK1)),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f3,axiom,(
% 1.89/1.01    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.89/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f12,plain,(
% 1.89/1.01    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.89/1.01    inference(ennf_transformation,[],[f3])).
% 1.89/1.01  
% 1.89/1.01  fof(f13,plain,(
% 1.89/1.01    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 1.89/1.01    inference(flattening,[],[f12])).
% 1.89/1.01  
% 1.89/1.01  fof(f35,plain,(
% 1.89/1.01    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f13])).
% 1.89/1.01  
% 1.89/1.01  fof(f2,axiom,(
% 1.89/1.01    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 1.89/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f10,plain,(
% 1.89/1.01    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.89/1.01    inference(ennf_transformation,[],[f2])).
% 1.89/1.01  
% 1.89/1.01  fof(f11,plain,(
% 1.89/1.01    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.89/1.01    inference(flattening,[],[f10])).
% 1.89/1.01  
% 1.89/1.01  fof(f34,plain,(
% 1.89/1.01    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f11])).
% 1.89/1.01  
% 1.89/1.01  fof(f4,axiom,(
% 1.89/1.01    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 1.89/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.01  
% 1.89/1.01  fof(f14,plain,(
% 1.89/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.89/1.01    inference(ennf_transformation,[],[f4])).
% 1.89/1.01  
% 1.89/1.01  fof(f15,plain,(
% 1.89/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.89/1.01    inference(flattening,[],[f14])).
% 1.89/1.01  
% 1.89/1.01  fof(f21,plain,(
% 1.89/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.89/1.01    inference(nnf_transformation,[],[f15])).
% 1.89/1.01  
% 1.89/1.01  fof(f22,plain,(
% 1.89/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.89/1.01    inference(flattening,[],[f21])).
% 1.89/1.01  
% 1.89/1.01  fof(f23,plain,(
% 1.89/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.89/1.01    inference(rectify,[],[f22])).
% 1.89/1.01  
% 1.89/1.01  fof(f24,plain,(
% 1.89/1.01    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 1.89/1.01    introduced(choice_axiom,[])).
% 1.89/1.01  
% 1.89/1.01  fof(f25,plain,(
% 1.89/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.89/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 1.89/1.01  
% 1.89/1.01  fof(f40,plain,(
% 1.89/1.01    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f25])).
% 1.89/1.01  
% 1.89/1.01  fof(f42,plain,(
% 1.89/1.01    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f25])).
% 1.89/1.01  
% 1.89/1.01  fof(f37,plain,(
% 1.89/1.01    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f25])).
% 1.89/1.01  
% 1.89/1.01  fof(f53,plain,(
% 1.89/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.89/1.01    inference(equality_resolution,[],[f37])).
% 1.89/1.01  
% 1.89/1.01  fof(f51,plain,(
% 1.89/1.01    ~r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2),
% 1.89/1.01    inference(cnf_transformation,[],[f31])).
% 1.89/1.01  
% 1.89/1.01  fof(f33,plain,(
% 1.89/1.01    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.89/1.01    inference(cnf_transformation,[],[f20])).
% 1.89/1.01  
% 1.89/1.01  cnf(c_14,negated_conjecture,
% 1.89/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_819,negated_conjecture,
% 1.89/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1144,plain,
% 1.89/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_15,negated_conjecture,
% 1.89/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_818,negated_conjecture,
% 1.89/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1145,plain,
% 1.89/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_11,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.89/1.01      | ~ v5_orders_2(X1)
% 1.89/1.01      | ~ v2_lattice3(X1)
% 1.89/1.01      | ~ l1_orders_2(X1)
% 1.89/1.01      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 1.89/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_16,negated_conjecture,
% 1.89/1.01      ( l1_orders_2(sK1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_613,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.89/1.01      | ~ v5_orders_2(X1)
% 1.89/1.01      | ~ v2_lattice3(X1)
% 1.89/1.01      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 1.89/1.01      | sK1 != X1 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_614,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ v5_orders_2(sK1)
% 1.89/1.01      | ~ v2_lattice3(sK1)
% 1.89/1.01      | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_613]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_18,negated_conjecture,
% 1.89/1.01      ( v5_orders_2(sK1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_17,negated_conjecture,
% 1.89/1.01      ( v2_lattice3(sK1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_618,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
% 1.89/1.01      inference(global_propositional_subsumption,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_614,c_18,c_17]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_619,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | k12_lattice3(sK1,X0,X1) = k11_lattice3(sK1,X0,X1) ),
% 1.89/1.01      inference(renaming,[status(thm)],[c_618]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_807,plain,
% 1.89/1.01      ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 1.89/1.01      | k12_lattice3(sK1,X0_43,X1_43) = k11_lattice3(sK1,X0_43,X1_43) ),
% 1.89/1.01      inference(subtyping,[status(esa)],[c_619]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1156,plain,
% 1.89/1.01      ( k12_lattice3(sK1,X0_43,X1_43) = k11_lattice3(sK1,X0_43,X1_43)
% 1.89/1.01      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 1.89/1.01      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1357,plain,
% 1.89/1.01      ( k12_lattice3(sK1,sK2,X0_43) = k11_lattice3(sK1,sK2,X0_43)
% 1.89/1.01      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1145,c_1156]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1615,plain,
% 1.89/1.01      ( k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
% 1.89/1.01      inference(superposition,[status(thm)],[c_1144,c_1357]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_13,negated_conjecture,
% 1.89/1.01      ( r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_180,plain,
% 1.89/1.01      ( r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.01      inference(prop_impl,[status(thm)],[c_13]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1,plain,
% 1.89/1.01      ( r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ r3_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | v2_struct_0(X0)
% 1.89/1.01      | ~ v3_orders_2(X0)
% 1.89/1.01      | ~ l1_orders_2(X0) ),
% 1.89/1.01      inference(cnf_transformation,[],[f32]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_19,negated_conjecture,
% 1.89/1.01      ( v3_orders_2(sK1) ),
% 1.89/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_315,plain,
% 1.89/1.01      ( r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ r3_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | v2_struct_0(X0)
% 1.89/1.01      | ~ l1_orders_2(X0)
% 1.89/1.01      | sK1 != X0 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_316,plain,
% 1.89/1.01      ( r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r3_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | v2_struct_0(sK1)
% 1.89/1.01      | ~ l1_orders_2(sK1) ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_315]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_3,plain,
% 1.89/1.01      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 1.89/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_49,plain,
% 1.89/1.01      ( ~ v2_lattice3(sK1) | ~ v2_struct_0(sK1) | ~ l1_orders_2(sK1) ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_318,plain,
% 1.89/1.01      ( r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r3_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(global_propositional_subsumption,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_316,c_17,c_16,c_49]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_319,plain,
% 1.89/1.01      ( r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r3_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(renaming,[status(thm)],[c_318]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_374,plain,
% 1.89/1.01      ( r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | k12_lattice3(sK1,sK2,sK3) = sK2
% 1.89/1.01      | sK3 != X1
% 1.89/1.01      | sK2 != X0
% 1.89/1.01      | sK1 != sK1 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_180,c_319]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_375,plain,
% 1.89/1.01      ( r1_orders_2(sK1,sK2,sK3)
% 1.89/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.89/1.01      | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_374]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_377,plain,
% 1.89/1.01      ( r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.01      inference(global_propositional_subsumption,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_375,c_15,c_14]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_732,plain,
% 1.89/1.01      ( r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.01      inference(prop_impl,[status(thm)],[c_15,c_14,c_375]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_816,plain,
% 1.89/1.01      ( r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.01      inference(subtyping,[status(esa)],[c_732]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1147,plain,
% 1.89/1.01      ( k12_lattice3(sK1,sK2,sK3) = sK2
% 1.89/1.01      | r1_orders_2(sK1,sK2,sK3) = iProver_top ),
% 1.89/1.01      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_821,plain,( X0_43 = X0_43 ),theory(equality) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_830,plain,
% 1.89/1.01      ( sK2 = sK2 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_821]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_2,plain,
% 1.89/1.01      ( r1_orders_2(X0,X1,X1)
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | v2_struct_0(X0)
% 1.89/1.01      | ~ v3_orders_2(X0)
% 1.89/1.01      | ~ l1_orders_2(X0) ),
% 1.89/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_297,plain,
% 1.89/1.01      ( r1_orders_2(X0,X1,X1)
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | v2_struct_0(X0)
% 1.89/1.01      | ~ l1_orders_2(X0)
% 1.89/1.01      | sK1 != X0 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_19]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_298,plain,
% 1.89/1.01      ( r1_orders_2(sK1,X0,X0)
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | v2_struct_0(sK1)
% 1.89/1.01      | ~ l1_orders_2(sK1) ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_297]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_302,plain,
% 1.89/1.01      ( r1_orders_2(sK1,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(global_propositional_subsumption,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_298,c_17,c_16,c_49]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_817,plain,
% 1.89/1.01      ( r1_orders_2(sK1,X0_43,X0_43)
% 1.89/1.01      | ~ m1_subset_1(X0_43,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(subtyping,[status(esa)],[c_302]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_834,plain,
% 1.89/1.01      ( r1_orders_2(sK1,sK2,sK2) | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_817]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_822,plain,
% 1.89/1.01      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 1.89/1.01      theory(equality) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1297,plain,
% 1.89/1.01      ( k12_lattice3(sK1,sK2,sK3) != X0_43
% 1.89/1.01      | k12_lattice3(sK1,sK2,sK3) = sK2
% 1.89/1.01      | sK2 != X0_43 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_822]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1333,plain,
% 1.89/1.01      ( k12_lattice3(sK1,sK2,sK3) != k11_lattice3(sK1,sK2,sK3)
% 1.89/1.01      | k12_lattice3(sK1,sK2,sK3) = sK2
% 1.89/1.01      | sK2 != k11_lattice3(sK1,sK2,sK3) ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_1297]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1334,plain,
% 1.89/1.01      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.89/1.01      | k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_807]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1344,plain,
% 1.89/1.01      ( k11_lattice3(sK1,sK2,sK3) != X0_43
% 1.89/1.01      | sK2 != X0_43
% 1.89/1.01      | sK2 = k11_lattice3(sK1,sK2,sK3) ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_822]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1345,plain,
% 1.89/1.01      ( k11_lattice3(sK1,sK2,sK3) != sK2
% 1.89/1.01      | sK2 = k11_lattice3(sK1,sK2,sK3)
% 1.89/1.01      | sK2 != sK2 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_1344]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_6,plain,
% 1.89/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X3)
% 1.89/1.01      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | ~ v5_orders_2(X0)
% 1.89/1.01      | ~ v2_lattice3(X0)
% 1.89/1.01      | v2_struct_0(X0)
% 1.89/1.01      | ~ l1_orders_2(X0)
% 1.89/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.89/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_134,plain,
% 1.89/1.01      ( ~ v2_lattice3(X0)
% 1.89/1.01      | ~ v5_orders_2(X0)
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X3)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ l1_orders_2(X0)
% 1.89/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.89/1.01      inference(global_propositional_subsumption,[status(thm)],[c_6,c_3]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_135,plain,
% 1.89/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X3)
% 1.89/1.01      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.01      | ~ v5_orders_2(X0)
% 1.89/1.01      | ~ v2_lattice3(X0)
% 1.89/1.01      | ~ l1_orders_2(X0)
% 1.89/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.89/1.01      inference(renaming,[status(thm)],[c_134]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_474,plain,
% 1.89/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X3)
% 1.89/1.01      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.01      | ~ v5_orders_2(X0)
% 1.89/1.01      | ~ v2_lattice3(X0)
% 1.89/1.01      | k11_lattice3(X0,X3,X2) = X1
% 1.89/1.01      | sK1 != X0 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_135,c_16]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_475,plain,
% 1.89/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 1.89/1.01      | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.89/1.01      | ~ v5_orders_2(sK1)
% 1.89/1.01      | ~ v2_lattice3(sK1)
% 1.89/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_474]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_477,plain,
% 1.89/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 1.89/1.01      | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.89/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 1.89/1.01      inference(global_propositional_subsumption,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_475,c_18,c_17]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_478,plain,
% 1.89/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 1.89/1.01      | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.89/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 1.89/1.01      inference(renaming,[status(thm)],[c_477]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_812,plain,
% 1.89/1.01      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 1.89/1.01      | ~ r1_orders_2(sK1,X0_43,X2_43)
% 1.89/1.01      | r1_orders_2(sK1,sK0(sK1,X2_43,X1_43,X0_43),X2_43)
% 1.89/1.01      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 1.89/1.01      | k11_lattice3(sK1,X2_43,X1_43) = X0_43 ),
% 1.89/1.01      inference(subtyping,[status(esa)],[c_478]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1389,plain,
% 1.89/1.01      ( ~ r1_orders_2(sK1,X0_43,sK3)
% 1.89/1.01      | ~ r1_orders_2(sK1,X0_43,sK2)
% 1.89/1.01      | r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_43),sK2)
% 1.89/1.01      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.89/1.01      | k11_lattice3(sK1,sK2,sK3) = X0_43 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_812]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_1396,plain,
% 1.89/1.01      ( r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
% 1.89/1.01      | ~ r1_orders_2(sK1,sK2,sK3)
% 1.89/1.01      | ~ r1_orders_2(sK1,sK2,sK2)
% 1.89/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.89/1.01      | k11_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.01      inference(instantiation,[status(thm)],[c_1389]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_4,plain,
% 1.89/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X3)
% 1.89/1.01      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | ~ v5_orders_2(X0)
% 1.89/1.01      | ~ v2_lattice3(X0)
% 1.89/1.01      | v2_struct_0(X0)
% 1.89/1.01      | ~ l1_orders_2(X0)
% 1.89/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.89/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_146,plain,
% 1.89/1.01      ( ~ v2_lattice3(X0)
% 1.89/1.01      | ~ v5_orders_2(X0)
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X3)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ l1_orders_2(X0)
% 1.89/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.89/1.01      inference(global_propositional_subsumption,[status(thm)],[c_4,c_3]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_147,plain,
% 1.89/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X3)
% 1.89/1.01      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.01      | ~ v5_orders_2(X0)
% 1.89/1.01      | ~ v2_lattice3(X0)
% 1.89/1.01      | ~ l1_orders_2(X0)
% 1.89/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.89/1.01      inference(renaming,[status(thm)],[c_146]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_408,plain,
% 1.89/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 1.89/1.01      | ~ r1_orders_2(X0,X1,X3)
% 1.89/1.01      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.01      | ~ v5_orders_2(X0)
% 1.89/1.01      | ~ v2_lattice3(X0)
% 1.89/1.01      | k11_lattice3(X0,X3,X2) = X1
% 1.89/1.01      | sK1 != X0 ),
% 1.89/1.01      inference(resolution_lifted,[status(thm)],[c_147,c_16]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_409,plain,
% 1.89/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 1.89/1.01      | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.89/1.01      | ~ v5_orders_2(sK1)
% 1.89/1.01      | ~ v2_lattice3(sK1)
% 1.89/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 1.89/1.01      inference(unflattening,[status(thm)],[c_408]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_413,plain,
% 1.89/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 1.89/1.01      | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.89/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 1.89/1.01      inference(global_propositional_subsumption,
% 1.89/1.01                [status(thm)],
% 1.89/1.01                [c_409,c_18,c_17]) ).
% 1.89/1.01  
% 1.89/1.01  cnf(c_414,plain,
% 1.89/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 1.89/1.01      | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
% 1.89/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.89/1.02      | k11_lattice3(sK1,X2,X1) = X0 ),
% 1.89/1.02      inference(renaming,[status(thm)],[c_413]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_814,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,X0_43,X1_43)
% 1.89/1.02      | ~ r1_orders_2(sK1,X0_43,X2_43)
% 1.89/1.02      | ~ r1_orders_2(sK1,sK0(sK1,X2_43,X1_43,X0_43),X0_43)
% 1.89/1.02      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
% 1.89/1.02      | k11_lattice3(sK1,X2_43,X1_43) = X0_43 ),
% 1.89/1.02      inference(subtyping,[status(esa)],[c_414]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_1387,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,X0_43,sK3)
% 1.89/1.02      | ~ r1_orders_2(sK1,X0_43,sK2)
% 1.89/1.02      | ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_43),X0_43)
% 1.89/1.02      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.89/1.02      | k11_lattice3(sK1,sK2,sK3) = X0_43 ),
% 1.89/1.02      inference(instantiation,[status(thm)],[c_814]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_1404,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
% 1.89/1.02      | ~ r1_orders_2(sK1,sK2,sK3)
% 1.89/1.02      | ~ r1_orders_2(sK1,sK2,sK2)
% 1.89/1.02      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.89/1.02      | k11_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.02      inference(instantiation,[status(thm)],[c_1387]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_1512,plain,
% 1.89/1.02      ( k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.02      inference(global_propositional_subsumption,
% 1.89/1.02                [status(thm)],
% 1.89/1.02                [c_1147,c_15,c_14,c_830,c_834,c_816,c_1333,c_1334,c_1345,
% 1.89/1.02                 c_1396,c_1404]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_1620,plain,
% 1.89/1.02      ( k11_lattice3(sK1,sK2,sK3) = sK2 ),
% 1.89/1.02      inference(light_normalisation,[status(thm)],[c_1615,c_1512]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_9,plain,
% 1.89/1.02      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 1.89/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 1.89/1.02      | ~ v5_orders_2(X0)
% 1.89/1.02      | ~ v2_lattice3(X0)
% 1.89/1.02      | v2_struct_0(X0)
% 1.89/1.02      | ~ l1_orders_2(X0) ),
% 1.89/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_115,plain,
% 1.89/1.02      ( ~ v2_lattice3(X0)
% 1.89/1.02      | ~ v5_orders_2(X0)
% 1.89/1.02      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.02      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 1.89/1.02      | ~ l1_orders_2(X0) ),
% 1.89/1.02      inference(global_propositional_subsumption,[status(thm)],[c_9,c_3]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_116,plain,
% 1.89/1.02      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 1.89/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 1.89/1.02      | ~ v5_orders_2(X0)
% 1.89/1.02      | ~ v2_lattice3(X0)
% 1.89/1.02      | ~ l1_orders_2(X0) ),
% 1.89/1.02      inference(renaming,[status(thm)],[c_115]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_569,plain,
% 1.89/1.02      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 1.89/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 1.89/1.02      | ~ v5_orders_2(X0)
% 1.89/1.02      | ~ v2_lattice3(X0)
% 1.89/1.02      | sK1 != X0 ),
% 1.89/1.02      inference(resolution_lifted,[status(thm)],[c_116,c_16]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_570,plain,
% 1.89/1.02      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
% 1.89/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1))
% 1.89/1.02      | ~ v5_orders_2(sK1)
% 1.89/1.02      | ~ v2_lattice3(sK1) ),
% 1.89/1.02      inference(unflattening,[status(thm)],[c_569]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_574,plain,
% 1.89/1.02      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
% 1.89/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
% 1.89/1.02      inference(global_propositional_subsumption,
% 1.89/1.02                [status(thm)],
% 1.89/1.02                [c_570,c_18,c_17]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_575,plain,
% 1.89/1.02      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
% 1.89/1.02      inference(renaming,[status(thm)],[c_574]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_809,plain,
% 1.89/1.02      ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X1_43)
% 1.89/1.02      | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) ),
% 1.89/1.02      inference(subtyping,[status(esa)],[c_575]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_1154,plain,
% 1.89/1.02      ( r1_orders_2(sK1,k11_lattice3(sK1,X0_43,X1_43),X1_43) = iProver_top
% 1.89/1.02      | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
% 1.89/1.02      | m1_subset_1(X1_43,u1_struct_0(sK1)) != iProver_top
% 1.89/1.02      | m1_subset_1(k11_lattice3(sK1,X0_43,X1_43),u1_struct_0(sK1)) != iProver_top ),
% 1.89/1.02      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_2125,plain,
% 1.89/1.02      ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK3) = iProver_top
% 1.89/1.02      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 1.89/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.89/1.02      inference(superposition,[status(thm)],[c_1620,c_1154]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_2137,plain,
% 1.89/1.02      ( r1_orders_2(sK1,sK2,sK3) = iProver_top
% 1.89/1.02      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 1.89/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.89/1.02      inference(light_normalisation,[status(thm)],[c_2125,c_1620]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_12,negated_conjecture,
% 1.89/1.02      ( ~ r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 1.89/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_178,plain,
% 1.89/1.02      ( ~ r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 1.89/1.02      inference(prop_impl,[status(thm)],[c_12]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_0,plain,
% 1.89/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 1.89/1.02      | r3_orders_2(X0,X1,X2)
% 1.89/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.02      | v2_struct_0(X0)
% 1.89/1.02      | ~ v3_orders_2(X0)
% 1.89/1.02      | ~ l1_orders_2(X0) ),
% 1.89/1.02      inference(cnf_transformation,[],[f33]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_335,plain,
% 1.89/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 1.89/1.02      | r3_orders_2(X0,X1,X2)
% 1.89/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.02      | v2_struct_0(X0)
% 1.89/1.02      | ~ l1_orders_2(X0)
% 1.89/1.02      | sK1 != X0 ),
% 1.89/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_336,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.02      | r3_orders_2(sK1,X0,X1)
% 1.89/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.02      | v2_struct_0(sK1)
% 1.89/1.02      | ~ l1_orders_2(sK1) ),
% 1.89/1.02      inference(unflattening,[status(thm)],[c_335]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_340,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.02      | r3_orders_2(sK1,X0,X1)
% 1.89/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.89/1.02      inference(global_propositional_subsumption,
% 1.89/1.02                [status(thm)],
% 1.89/1.02                [c_336,c_17,c_16,c_49]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_341,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.02      | r3_orders_2(sK1,X0,X1)
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.89/1.02      inference(renaming,[status(thm)],[c_340]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_388,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,X0,X1)
% 1.89/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.89/1.02      | k12_lattice3(sK1,sK2,sK3) != sK2
% 1.89/1.02      | sK3 != X1
% 1.89/1.02      | sK2 != X0
% 1.89/1.02      | sK1 != sK1 ),
% 1.89/1.02      inference(resolution_lifted,[status(thm)],[c_178,c_341]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_389,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,sK2,sK3)
% 1.89/1.02      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.89/1.02      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.89/1.02      | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 1.89/1.02      inference(unflattening,[status(thm)],[c_388]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_391,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 1.89/1.02      inference(global_propositional_subsumption,
% 1.89/1.02                [status(thm)],
% 1.89/1.02                [c_389,c_15,c_14]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_730,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 1.89/1.02      inference(prop_impl,[status(thm)],[c_15,c_14,c_389]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_815,plain,
% 1.89/1.02      ( ~ r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 1.89/1.02      inference(subtyping,[status(esa)],[c_730]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_837,plain,
% 1.89/1.02      ( k12_lattice3(sK1,sK2,sK3) != sK2
% 1.89/1.02      | r1_orders_2(sK1,sK2,sK3) != iProver_top ),
% 1.89/1.02      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_25,plain,
% 1.89/1.02      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 1.89/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(c_24,plain,
% 1.89/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.89/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.89/1.02  
% 1.89/1.02  cnf(contradiction,plain,
% 1.89/1.02      ( $false ),
% 1.89/1.02      inference(minisat,[status(thm)],[c_2137,c_1512,c_837,c_25,c_24]) ).
% 1.89/1.02  
% 1.89/1.02  
% 1.89/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.89/1.02  
% 1.89/1.02  ------                               Statistics
% 1.89/1.02  
% 1.89/1.02  ------ General
% 1.89/1.02  
% 1.89/1.02  abstr_ref_over_cycles:                  0
% 1.89/1.02  abstr_ref_under_cycles:                 0
% 1.89/1.02  gc_basic_clause_elim:                   0
% 1.89/1.02  forced_gc_time:                         0
% 1.89/1.02  parsing_time:                           0.014
% 1.89/1.02  unif_index_cands_time:                  0.
% 1.89/1.02  unif_index_add_time:                    0.
% 1.89/1.02  orderings_time:                         0.
% 1.89/1.02  out_proof_time:                         0.014
% 1.89/1.02  total_time:                             0.112
% 1.89/1.02  num_of_symbols:                         46
% 1.89/1.02  num_of_terms:                           1715
% 1.89/1.02  
% 1.89/1.02  ------ Preprocessing
% 1.89/1.02  
% 1.89/1.02  num_of_splits:                          0
% 1.89/1.02  num_of_split_atoms:                     0
% 1.89/1.02  num_of_reused_defs:                     0
% 1.89/1.02  num_eq_ax_congr_red:                    25
% 1.89/1.02  num_of_sem_filtered_clauses:            1
% 1.89/1.02  num_of_subtypes:                        3
% 1.89/1.02  monotx_restored_types:                  0
% 1.89/1.02  sat_num_of_epr_types:                   0
% 1.89/1.02  sat_num_of_non_cyclic_types:            0
% 1.89/1.02  sat_guarded_non_collapsed_types:        1
% 1.89/1.02  num_pure_diseq_elim:                    0
% 1.89/1.02  simp_replaced_by:                       0
% 1.89/1.02  res_preprocessed:                       70
% 1.89/1.02  prep_upred:                             0
% 1.89/1.02  prep_unflattend:                        15
% 1.89/1.02  smt_new_axioms:                         0
% 1.89/1.02  pred_elim_cands:                        2
% 1.89/1.02  pred_elim:                              6
% 1.89/1.02  pred_elim_cl:                           7
% 1.89/1.02  pred_elim_cycles:                       8
% 1.89/1.02  merged_defs:                            8
% 1.89/1.02  merged_defs_ncl:                        0
% 1.89/1.02  bin_hyper_res:                          8
% 1.89/1.02  prep_cycles:                            4
% 1.89/1.02  pred_elim_time:                         0.009
% 1.89/1.02  splitting_time:                         0.
% 1.89/1.02  sem_filter_time:                        0.
% 1.89/1.02  monotx_time:                            0.
% 1.89/1.02  subtype_inf_time:                       0.
% 1.89/1.02  
% 1.89/1.02  ------ Problem properties
% 1.89/1.02  
% 1.89/1.02  clauses:                                13
% 1.89/1.02  conjectures:                            2
% 1.89/1.02  epr:                                    0
% 1.89/1.02  horn:                                   9
% 1.89/1.02  ground:                                 4
% 1.89/1.02  unary:                                  2
% 1.89/1.02  binary:                                 3
% 1.89/1.02  lits:                                   54
% 1.89/1.02  lits_eq:                                7
% 1.89/1.02  fd_pure:                                0
% 1.89/1.02  fd_pseudo:                              0
% 1.89/1.02  fd_cond:                                0
% 1.89/1.02  fd_pseudo_cond:                         4
% 1.89/1.02  ac_symbols:                             0
% 1.89/1.02  
% 1.89/1.02  ------ Propositional Solver
% 1.89/1.02  
% 1.89/1.02  prop_solver_calls:                      26
% 1.89/1.02  prop_fast_solver_calls:                 869
% 1.89/1.02  smt_solver_calls:                       0
% 1.89/1.02  smt_fast_solver_calls:                  0
% 1.89/1.02  prop_num_of_clauses:                    583
% 1.89/1.02  prop_preprocess_simplified:             2410
% 1.89/1.02  prop_fo_subsumed:                       35
% 1.89/1.02  prop_solver_time:                       0.
% 1.89/1.02  smt_solver_time:                        0.
% 1.89/1.02  smt_fast_solver_time:                   0.
% 1.89/1.02  prop_fast_solver_time:                  0.
% 1.89/1.02  prop_unsat_core_time:                   0.
% 1.89/1.02  
% 1.89/1.02  ------ QBF
% 1.89/1.02  
% 1.89/1.02  qbf_q_res:                              0
% 1.89/1.02  qbf_num_tautologies:                    0
% 1.89/1.02  qbf_prep_cycles:                        0
% 1.89/1.02  
% 1.89/1.02  ------ BMC1
% 1.89/1.02  
% 1.89/1.02  bmc1_current_bound:                     -1
% 1.89/1.02  bmc1_last_solved_bound:                 -1
% 1.89/1.02  bmc1_unsat_core_size:                   -1
% 1.89/1.02  bmc1_unsat_core_parents_size:           -1
% 1.89/1.02  bmc1_merge_next_fun:                    0
% 1.89/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.89/1.02  
% 1.89/1.02  ------ Instantiation
% 1.89/1.02  
% 1.89/1.02  inst_num_of_clauses:                    162
% 1.89/1.02  inst_num_in_passive:                    36
% 1.89/1.02  inst_num_in_active:                     92
% 1.89/1.02  inst_num_in_unprocessed:                34
% 1.89/1.02  inst_num_of_loops:                      110
% 1.89/1.02  inst_num_of_learning_restarts:          0
% 1.89/1.02  inst_num_moves_active_passive:          14
% 1.89/1.02  inst_lit_activity:                      0
% 1.89/1.02  inst_lit_activity_moves:                0
% 1.89/1.02  inst_num_tautologies:                   0
% 1.89/1.02  inst_num_prop_implied:                  0
% 1.89/1.02  inst_num_existing_simplified:           0
% 1.89/1.02  inst_num_eq_res_simplified:             0
% 1.89/1.02  inst_num_child_elim:                    0
% 1.89/1.02  inst_num_of_dismatching_blockings:      32
% 1.89/1.02  inst_num_of_non_proper_insts:           131
% 1.89/1.02  inst_num_of_duplicates:                 0
% 1.89/1.02  inst_inst_num_from_inst_to_res:         0
% 1.89/1.02  inst_dismatching_checking_time:         0.
% 1.89/1.02  
% 1.89/1.02  ------ Resolution
% 1.89/1.02  
% 1.89/1.02  res_num_of_clauses:                     0
% 1.89/1.02  res_num_in_passive:                     0
% 1.89/1.02  res_num_in_active:                      0
% 1.89/1.02  res_num_of_loops:                       74
% 1.89/1.02  res_forward_subset_subsumed:            18
% 1.89/1.02  res_backward_subset_subsumed:           0
% 1.89/1.02  res_forward_subsumed:                   0
% 1.89/1.02  res_backward_subsumed:                  0
% 1.89/1.02  res_forward_subsumption_resolution:     0
% 1.89/1.02  res_backward_subsumption_resolution:    0
% 1.89/1.02  res_clause_to_clause_subsumption:       201
% 1.89/1.02  res_orphan_elimination:                 0
% 1.89/1.02  res_tautology_del:                      29
% 1.89/1.02  res_num_eq_res_simplified:              0
% 1.89/1.02  res_num_sel_changes:                    0
% 1.89/1.02  res_moves_from_active_to_pass:          0
% 1.89/1.02  
% 1.89/1.02  ------ Superposition
% 1.89/1.02  
% 1.89/1.02  sup_time_total:                         0.
% 1.89/1.02  sup_time_generating:                    0.
% 1.89/1.02  sup_time_sim_full:                      0.
% 1.89/1.02  sup_time_sim_immed:                     0.
% 1.89/1.02  
% 1.89/1.02  sup_num_of_clauses:                     28
% 1.89/1.02  sup_num_in_active:                      21
% 1.89/1.02  sup_num_in_passive:                     7
% 1.89/1.02  sup_num_of_loops:                       20
% 1.89/1.02  sup_fw_superposition:                   8
% 1.89/1.02  sup_bw_superposition:                   9
% 1.89/1.02  sup_immediate_simplified:               4
% 1.89/1.02  sup_given_eliminated:                   0
% 1.89/1.02  comparisons_done:                       0
% 1.89/1.02  comparisons_avoided:                    0
% 1.89/1.02  
% 1.89/1.02  ------ Simplifications
% 1.89/1.02  
% 1.89/1.02  
% 1.89/1.02  sim_fw_subset_subsumed:                 0
% 1.89/1.02  sim_bw_subset_subsumed:                 0
% 1.89/1.02  sim_fw_subsumed:                        1
% 1.89/1.02  sim_bw_subsumed:                        0
% 1.89/1.02  sim_fw_subsumption_res:                 0
% 1.89/1.02  sim_bw_subsumption_res:                 0
% 1.89/1.02  sim_tautology_del:                      1
% 1.89/1.02  sim_eq_tautology_del:                   0
% 1.89/1.02  sim_eq_res_simp:                        0
% 1.89/1.02  sim_fw_demodulated:                     0
% 1.89/1.02  sim_bw_demodulated:                     0
% 1.89/1.02  sim_light_normalised:                   4
% 1.89/1.02  sim_joinable_taut:                      0
% 1.89/1.02  sim_joinable_simp:                      0
% 1.89/1.02  sim_ac_normalised:                      0
% 1.89/1.02  sim_smt_subsumption:                    0
% 1.89/1.02  
%------------------------------------------------------------------------------
