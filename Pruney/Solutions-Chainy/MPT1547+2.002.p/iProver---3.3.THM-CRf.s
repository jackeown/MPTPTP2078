%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:33 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  152 (2653 expanded)
%              Number of clauses        :  104 ( 591 expanded)
%              Number of leaves         :   12 ( 713 expanded)
%              Depth                    :   22
%              Number of atoms          :  840 (20986 expanded)
%              Number of equality atoms :  142 (3884 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).

fof(f53,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
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

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

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
    inference(flattening,[],[f24])).

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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f55,plain,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_928,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1334,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_927,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1335,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_700,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k12_lattice3(sK1,X0,X1) = k11_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_19,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_705,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k12_lattice3(sK1,X0,X1) = k11_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_701,c_19,c_18])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
    inference(renaming,[status(thm)],[c_705])).

cnf(c_915,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | k12_lattice3(sK1,X1_44,X0_44) = k11_lattice3(sK1,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_706])).

cnf(c_1349,plain,
    ( k12_lattice3(sK1,X0_44,X1_44) = k11_lattice3(sK1,X0_44,X1_44)
    | m1_subset_1(X1_44,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_915])).

cnf(c_1639,plain,
    ( k12_lattice3(sK1,sK2,X0_44) = k11_lattice3(sK1,sK2,X0_44)
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_1349])).

cnf(c_1767,plain,
    ( k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1334,c_1639])).

cnf(c_14,negated_conjecture,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_190,plain,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_332,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_333,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_53,plain,
    ( ~ v2_lattice3(sK1)
    | ~ v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_337,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_18,c_17,c_53])).

cnf(c_338,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_417,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK2
    | sK3 != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_338])).

cnf(c_418,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_420,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_16,c_15])).

cnf(c_828,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(prop_impl,[status(thm)],[c_16,c_15,c_418])).

cnf(c_926,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_828])).

cnf(c_1336,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_934,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_943,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_2,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_311,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_312,plain,
    ( r3_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( r3_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_18,c_17,c_53])).

cnf(c_317,plain,
    ( r3_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_445,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 != X3
    | X0 != X3
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_338])).

cnf(c_446,plain,
    ( r1_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_924,plain,
    ( r1_orders_2(sK1,X0_44,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_446])).

cnf(c_931,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_924])).

cnf(c_930,plain,
    ( r1_orders_2(sK1,X0_44,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_924])).

cnf(c_950,plain,
    ( r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_929,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_924])).

cnf(c_953,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_935,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1520,plain,
    ( k12_lattice3(sK1,sK2,sK3) != X0_44
    | k12_lattice3(sK1,sK2,sK3) = sK2
    | sK2 != X0_44 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1568,plain,
    ( k12_lattice3(sK1,sK2,sK3) != k11_lattice3(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2
    | sK2 != k11_lattice3(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_1569,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_1579,plain,
    ( k11_lattice3(sK1,sK2,sK3) != X0_44
    | sK2 != X0_44
    | sK2 = k11_lattice3(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1580,plain,
    ( k11_lattice3(sK1,sK2,sK3) != sK2
    | sK2 = k11_lattice3(sK1,sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1579])).

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
    inference(cnf_transformation,[],[f43])).

cnf(c_143,plain,
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

cnf(c_144,plain,
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
    inference(renaming,[status(thm)],[c_143])).

cnf(c_540,plain,
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
    inference(resolution_lifted,[status(thm)],[c_144,c_17])).

cnf(c_541,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_543,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_19,c_18])).

cnf(c_544,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_921,plain,
    ( ~ r1_orders_2(sK1,X0_44,X1_44)
    | ~ r1_orders_2(sK1,X0_44,X2_44)
    | r1_orders_2(sK1,sK0(sK1,X2_44,X1_44,X0_44),X2_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_44,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2_44,X1_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_544])).

cnf(c_1614,plain,
    ( ~ r1_orders_2(sK1,X0_44,sK3)
    | ~ r1_orders_2(sK1,X0_44,sK2)
    | r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_44),sK2)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = X0_44 ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_1621,plain,
    ( r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
    | ~ r1_orders_2(sK1,sK2,sK3)
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_1614])).

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
    inference(cnf_transformation,[],[f45])).

cnf(c_155,plain,
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

cnf(c_156,plain,
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
    inference(renaming,[status(thm)],[c_155])).

cnf(c_474,plain,
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
    inference(resolution_lifted,[status(thm)],[c_156,c_17])).

cnf(c_475,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_479,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_19,c_18])).

cnf(c_480,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_479])).

cnf(c_923,plain,
    ( ~ r1_orders_2(sK1,X0_44,X1_44)
    | ~ r1_orders_2(sK1,X0_44,X2_44)
    | ~ r1_orders_2(sK1,sK0(sK1,X2_44,X1_44,X0_44),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_44,u1_struct_0(sK1))
    | k11_lattice3(sK1,X2_44,X1_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_480])).

cnf(c_1612,plain,
    ( ~ r1_orders_2(sK1,X0_44,sK3)
    | ~ r1_orders_2(sK1,X0_44,sK2)
    | ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_44),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = X0_44 ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_1629,plain,
    ( ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
    | ~ r1_orders_2(sK1,sK2,sK3)
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k11_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_1736,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1336,c_16,c_15,c_943,c_926,c_931,c_950,c_953,c_1568,c_1569,c_1580,c_1621,c_1629])).

cnf(c_1772,plain,
    ( k11_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1767,c_1736])).

cnf(c_9,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_124,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_3])).

cnf(c_125,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_635,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_125,c_17])).

cnf(c_636,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_640,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_19,c_18])).

cnf(c_641,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_640])).

cnf(c_918,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0_44,X1_44),X1_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | ~ m1_subset_1(k11_lattice3(sK1,X0_44,X1_44),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_641])).

cnf(c_1346,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,X0_44,X1_44),X1_44) = iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_44,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k11_lattice3(sK1,X0_44,X1_44),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_2211,plain,
    ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_1346])).

cnf(c_2223,plain,
    ( r1_orders_2(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2211,c_1772])).

cnf(c_13,negated_conjecture,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_188,plain,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_356,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_357,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_361,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_18,c_17,c_53])).

cnf(c_362,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_431,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) != sK2
    | sK3 != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_188,c_362])).

cnf(c_432,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_434,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_16,c_15])).

cnf(c_826,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(prop_impl,[status(thm)],[c_16,c_15,c_432])).

cnf(c_925,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_826])).

cnf(c_947,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK2
    | r1_orders_2(sK1,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2223,c_1736,c_947,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.25/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.01  
% 2.25/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.25/1.01  
% 2.25/1.01  ------  iProver source info
% 2.25/1.01  
% 2.25/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.25/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.25/1.01  git: non_committed_changes: false
% 2.25/1.01  git: last_make_outside_of_git: false
% 2.25/1.01  
% 2.25/1.01  ------ 
% 2.25/1.01  
% 2.25/1.01  ------ Input Options
% 2.25/1.01  
% 2.25/1.01  --out_options                           all
% 2.25/1.01  --tptp_safe_out                         true
% 2.25/1.01  --problem_path                          ""
% 2.25/1.01  --include_path                          ""
% 2.25/1.01  --clausifier                            res/vclausify_rel
% 2.25/1.01  --clausifier_options                    --mode clausify
% 2.25/1.01  --stdin                                 false
% 2.25/1.01  --stats_out                             all
% 2.25/1.01  
% 2.25/1.01  ------ General Options
% 2.25/1.01  
% 2.25/1.01  --fof                                   false
% 2.25/1.01  --time_out_real                         305.
% 2.25/1.01  --time_out_virtual                      -1.
% 2.25/1.01  --symbol_type_check                     false
% 2.25/1.01  --clausify_out                          false
% 2.25/1.01  --sig_cnt_out                           false
% 2.25/1.01  --trig_cnt_out                          false
% 2.25/1.01  --trig_cnt_out_tolerance                1.
% 2.25/1.01  --trig_cnt_out_sk_spl                   false
% 2.25/1.01  --abstr_cl_out                          false
% 2.25/1.01  
% 2.25/1.01  ------ Global Options
% 2.25/1.01  
% 2.25/1.01  --schedule                              default
% 2.25/1.01  --add_important_lit                     false
% 2.25/1.01  --prop_solver_per_cl                    1000
% 2.25/1.01  --min_unsat_core                        false
% 2.25/1.01  --soft_assumptions                      false
% 2.25/1.01  --soft_lemma_size                       3
% 2.25/1.01  --prop_impl_unit_size                   0
% 2.25/1.01  --prop_impl_unit                        []
% 2.25/1.01  --share_sel_clauses                     true
% 2.25/1.01  --reset_solvers                         false
% 2.25/1.01  --bc_imp_inh                            [conj_cone]
% 2.25/1.01  --conj_cone_tolerance                   3.
% 2.25/1.01  --extra_neg_conj                        none
% 2.25/1.01  --large_theory_mode                     true
% 2.25/1.01  --prolific_symb_bound                   200
% 2.25/1.01  --lt_threshold                          2000
% 2.25/1.01  --clause_weak_htbl                      true
% 2.25/1.01  --gc_record_bc_elim                     false
% 2.25/1.01  
% 2.25/1.01  ------ Preprocessing Options
% 2.25/1.01  
% 2.25/1.01  --preprocessing_flag                    true
% 2.25/1.01  --time_out_prep_mult                    0.1
% 2.25/1.01  --splitting_mode                        input
% 2.25/1.01  --splitting_grd                         true
% 2.25/1.01  --splitting_cvd                         false
% 2.25/1.01  --splitting_cvd_svl                     false
% 2.25/1.01  --splitting_nvd                         32
% 2.25/1.01  --sub_typing                            true
% 2.25/1.01  --prep_gs_sim                           true
% 2.25/1.01  --prep_unflatten                        true
% 2.25/1.01  --prep_res_sim                          true
% 2.25/1.01  --prep_upred                            true
% 2.25/1.01  --prep_sem_filter                       exhaustive
% 2.25/1.01  --prep_sem_filter_out                   false
% 2.25/1.01  --pred_elim                             true
% 2.25/1.01  --res_sim_input                         true
% 2.25/1.01  --eq_ax_congr_red                       true
% 2.25/1.01  --pure_diseq_elim                       true
% 2.25/1.01  --brand_transform                       false
% 2.25/1.01  --non_eq_to_eq                          false
% 2.25/1.01  --prep_def_merge                        true
% 2.25/1.01  --prep_def_merge_prop_impl              false
% 2.25/1.01  --prep_def_merge_mbd                    true
% 2.25/1.01  --prep_def_merge_tr_red                 false
% 2.25/1.01  --prep_def_merge_tr_cl                  false
% 2.25/1.01  --smt_preprocessing                     true
% 2.25/1.01  --smt_ac_axioms                         fast
% 2.25/1.01  --preprocessed_out                      false
% 2.25/1.01  --preprocessed_stats                    false
% 2.25/1.01  
% 2.25/1.01  ------ Abstraction refinement Options
% 2.25/1.01  
% 2.25/1.01  --abstr_ref                             []
% 2.25/1.01  --abstr_ref_prep                        false
% 2.25/1.01  --abstr_ref_until_sat                   false
% 2.25/1.01  --abstr_ref_sig_restrict                funpre
% 2.25/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/1.01  --abstr_ref_under                       []
% 2.25/1.01  
% 2.25/1.01  ------ SAT Options
% 2.25/1.01  
% 2.25/1.01  --sat_mode                              false
% 2.25/1.01  --sat_fm_restart_options                ""
% 2.25/1.01  --sat_gr_def                            false
% 2.25/1.01  --sat_epr_types                         true
% 2.25/1.01  --sat_non_cyclic_types                  false
% 2.25/1.01  --sat_finite_models                     false
% 2.25/1.01  --sat_fm_lemmas                         false
% 2.25/1.01  --sat_fm_prep                           false
% 2.25/1.01  --sat_fm_uc_incr                        true
% 2.25/1.01  --sat_out_model                         small
% 2.25/1.01  --sat_out_clauses                       false
% 2.25/1.01  
% 2.25/1.01  ------ QBF Options
% 2.25/1.01  
% 2.25/1.01  --qbf_mode                              false
% 2.25/1.01  --qbf_elim_univ                         false
% 2.25/1.01  --qbf_dom_inst                          none
% 2.25/1.01  --qbf_dom_pre_inst                      false
% 2.25/1.01  --qbf_sk_in                             false
% 2.25/1.01  --qbf_pred_elim                         true
% 2.25/1.01  --qbf_split                             512
% 2.25/1.01  
% 2.25/1.01  ------ BMC1 Options
% 2.25/1.01  
% 2.25/1.01  --bmc1_incremental                      false
% 2.25/1.01  --bmc1_axioms                           reachable_all
% 2.25/1.01  --bmc1_min_bound                        0
% 2.25/1.01  --bmc1_max_bound                        -1
% 2.25/1.01  --bmc1_max_bound_default                -1
% 2.25/1.01  --bmc1_symbol_reachability              true
% 2.25/1.01  --bmc1_property_lemmas                  false
% 2.25/1.01  --bmc1_k_induction                      false
% 2.25/1.01  --bmc1_non_equiv_states                 false
% 2.25/1.01  --bmc1_deadlock                         false
% 2.25/1.01  --bmc1_ucm                              false
% 2.25/1.01  --bmc1_add_unsat_core                   none
% 2.25/1.01  --bmc1_unsat_core_children              false
% 2.25/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/1.01  --bmc1_out_stat                         full
% 2.25/1.01  --bmc1_ground_init                      false
% 2.25/1.01  --bmc1_pre_inst_next_state              false
% 2.25/1.01  --bmc1_pre_inst_state                   false
% 2.25/1.01  --bmc1_pre_inst_reach_state             false
% 2.25/1.01  --bmc1_out_unsat_core                   false
% 2.25/1.01  --bmc1_aig_witness_out                  false
% 2.25/1.01  --bmc1_verbose                          false
% 2.25/1.01  --bmc1_dump_clauses_tptp                false
% 2.25/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.25/1.01  --bmc1_dump_file                        -
% 2.25/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.25/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.25/1.01  --bmc1_ucm_extend_mode                  1
% 2.25/1.01  --bmc1_ucm_init_mode                    2
% 2.25/1.01  --bmc1_ucm_cone_mode                    none
% 2.25/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.25/1.01  --bmc1_ucm_relax_model                  4
% 2.25/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.25/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/1.01  --bmc1_ucm_layered_model                none
% 2.25/1.01  --bmc1_ucm_max_lemma_size               10
% 2.25/1.01  
% 2.25/1.01  ------ AIG Options
% 2.25/1.01  
% 2.25/1.01  --aig_mode                              false
% 2.25/1.01  
% 2.25/1.01  ------ Instantiation Options
% 2.25/1.01  
% 2.25/1.01  --instantiation_flag                    true
% 2.25/1.01  --inst_sos_flag                         false
% 2.25/1.01  --inst_sos_phase                        true
% 2.25/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/1.01  --inst_lit_sel_side                     num_symb
% 2.25/1.01  --inst_solver_per_active                1400
% 2.25/1.01  --inst_solver_calls_frac                1.
% 2.25/1.01  --inst_passive_queue_type               priority_queues
% 2.25/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/1.01  --inst_passive_queues_freq              [25;2]
% 2.25/1.01  --inst_dismatching                      true
% 2.25/1.01  --inst_eager_unprocessed_to_passive     true
% 2.25/1.01  --inst_prop_sim_given                   true
% 2.25/1.01  --inst_prop_sim_new                     false
% 2.25/1.01  --inst_subs_new                         false
% 2.25/1.01  --inst_eq_res_simp                      false
% 2.25/1.01  --inst_subs_given                       false
% 2.25/1.01  --inst_orphan_elimination               true
% 2.25/1.01  --inst_learning_loop_flag               true
% 2.25/1.01  --inst_learning_start                   3000
% 2.25/1.01  --inst_learning_factor                  2
% 2.25/1.01  --inst_start_prop_sim_after_learn       3
% 2.25/1.01  --inst_sel_renew                        solver
% 2.25/1.01  --inst_lit_activity_flag                true
% 2.25/1.01  --inst_restr_to_given                   false
% 2.25/1.01  --inst_activity_threshold               500
% 2.25/1.01  --inst_out_proof                        true
% 2.25/1.01  
% 2.25/1.01  ------ Resolution Options
% 2.25/1.01  
% 2.25/1.01  --resolution_flag                       true
% 2.25/1.01  --res_lit_sel                           adaptive
% 2.25/1.01  --res_lit_sel_side                      none
% 2.25/1.01  --res_ordering                          kbo
% 2.25/1.01  --res_to_prop_solver                    active
% 2.25/1.01  --res_prop_simpl_new                    false
% 2.25/1.01  --res_prop_simpl_given                  true
% 2.25/1.01  --res_passive_queue_type                priority_queues
% 2.25/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/1.01  --res_passive_queues_freq               [15;5]
% 2.25/1.01  --res_forward_subs                      full
% 2.25/1.01  --res_backward_subs                     full
% 2.25/1.01  --res_forward_subs_resolution           true
% 2.25/1.01  --res_backward_subs_resolution          true
% 2.25/1.01  --res_orphan_elimination                true
% 2.25/1.01  --res_time_limit                        2.
% 2.25/1.01  --res_out_proof                         true
% 2.25/1.01  
% 2.25/1.01  ------ Superposition Options
% 2.25/1.01  
% 2.25/1.01  --superposition_flag                    true
% 2.25/1.01  --sup_passive_queue_type                priority_queues
% 2.25/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.25/1.01  --demod_completeness_check              fast
% 2.25/1.01  --demod_use_ground                      true
% 2.25/1.01  --sup_to_prop_solver                    passive
% 2.25/1.01  --sup_prop_simpl_new                    true
% 2.25/1.01  --sup_prop_simpl_given                  true
% 2.25/1.01  --sup_fun_splitting                     false
% 2.25/1.01  --sup_smt_interval                      50000
% 2.25/1.01  
% 2.25/1.01  ------ Superposition Simplification Setup
% 2.25/1.01  
% 2.25/1.01  --sup_indices_passive                   []
% 2.25/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/1.01  --sup_full_bw                           [BwDemod]
% 2.25/1.01  --sup_immed_triv                        [TrivRules]
% 2.25/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/1.01  --sup_immed_bw_main                     []
% 2.25/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/1.01  
% 2.25/1.01  ------ Combination Options
% 2.25/1.01  
% 2.25/1.01  --comb_res_mult                         3
% 2.25/1.01  --comb_sup_mult                         2
% 2.25/1.01  --comb_inst_mult                        10
% 2.25/1.01  
% 2.25/1.01  ------ Debug Options
% 2.25/1.01  
% 2.25/1.01  --dbg_backtrace                         false
% 2.25/1.01  --dbg_dump_prop_clauses                 false
% 2.25/1.01  --dbg_dump_prop_clauses_file            -
% 2.25/1.01  --dbg_out_stat                          false
% 2.25/1.01  ------ Parsing...
% 2.25/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.25/1.01  
% 2.25/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.25/1.01  
% 2.25/1.01  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.25/1.01  
% 2.25/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.25/1.01  ------ Proving...
% 2.25/1.01  ------ Problem Properties 
% 2.25/1.01  
% 2.25/1.01  
% 2.25/1.01  clauses                                 18
% 2.25/1.01  conjectures                             2
% 2.25/1.01  EPR                                     2
% 2.25/1.01  Horn                                    12
% 2.25/1.01  unary                                   2
% 2.25/1.01  binary                                  5
% 2.25/1.01  lits                                    67
% 2.25/1.01  lits eq                                 9
% 2.25/1.01  fd_pure                                 0
% 2.25/1.01  fd_pseudo                               0
% 2.25/1.01  fd_cond                                 0
% 2.25/1.01  fd_pseudo_cond                          4
% 2.25/1.01  AC symbols                              0
% 2.25/1.01  
% 2.25/1.01  ------ Schedule dynamic 5 is on 
% 2.25/1.01  
% 2.25/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.25/1.01  
% 2.25/1.01  
% 2.25/1.01  ------ 
% 2.25/1.01  Current options:
% 2.25/1.01  ------ 
% 2.25/1.01  
% 2.25/1.01  ------ Input Options
% 2.25/1.01  
% 2.25/1.01  --out_options                           all
% 2.25/1.01  --tptp_safe_out                         true
% 2.25/1.01  --problem_path                          ""
% 2.25/1.01  --include_path                          ""
% 2.25/1.01  --clausifier                            res/vclausify_rel
% 2.25/1.01  --clausifier_options                    --mode clausify
% 2.25/1.01  --stdin                                 false
% 2.25/1.01  --stats_out                             all
% 2.25/1.01  
% 2.25/1.01  ------ General Options
% 2.25/1.01  
% 2.25/1.01  --fof                                   false
% 2.25/1.01  --time_out_real                         305.
% 2.25/1.01  --time_out_virtual                      -1.
% 2.25/1.01  --symbol_type_check                     false
% 2.25/1.01  --clausify_out                          false
% 2.25/1.01  --sig_cnt_out                           false
% 2.25/1.01  --trig_cnt_out                          false
% 2.25/1.01  --trig_cnt_out_tolerance                1.
% 2.25/1.01  --trig_cnt_out_sk_spl                   false
% 2.25/1.01  --abstr_cl_out                          false
% 2.25/1.01  
% 2.25/1.01  ------ Global Options
% 2.25/1.01  
% 2.25/1.01  --schedule                              default
% 2.25/1.01  --add_important_lit                     false
% 2.25/1.01  --prop_solver_per_cl                    1000
% 2.25/1.01  --min_unsat_core                        false
% 2.25/1.01  --soft_assumptions                      false
% 2.25/1.01  --soft_lemma_size                       3
% 2.25/1.01  --prop_impl_unit_size                   0
% 2.25/1.01  --prop_impl_unit                        []
% 2.25/1.01  --share_sel_clauses                     true
% 2.25/1.01  --reset_solvers                         false
% 2.25/1.01  --bc_imp_inh                            [conj_cone]
% 2.25/1.01  --conj_cone_tolerance                   3.
% 2.25/1.01  --extra_neg_conj                        none
% 2.25/1.01  --large_theory_mode                     true
% 2.25/1.01  --prolific_symb_bound                   200
% 2.25/1.01  --lt_threshold                          2000
% 2.25/1.01  --clause_weak_htbl                      true
% 2.25/1.01  --gc_record_bc_elim                     false
% 2.25/1.01  
% 2.25/1.01  ------ Preprocessing Options
% 2.25/1.01  
% 2.25/1.01  --preprocessing_flag                    true
% 2.25/1.01  --time_out_prep_mult                    0.1
% 2.25/1.01  --splitting_mode                        input
% 2.25/1.01  --splitting_grd                         true
% 2.25/1.01  --splitting_cvd                         false
% 2.25/1.01  --splitting_cvd_svl                     false
% 2.25/1.01  --splitting_nvd                         32
% 2.25/1.01  --sub_typing                            true
% 2.25/1.01  --prep_gs_sim                           true
% 2.25/1.01  --prep_unflatten                        true
% 2.25/1.01  --prep_res_sim                          true
% 2.25/1.01  --prep_upred                            true
% 2.25/1.01  --prep_sem_filter                       exhaustive
% 2.25/1.01  --prep_sem_filter_out                   false
% 2.25/1.01  --pred_elim                             true
% 2.25/1.01  --res_sim_input                         true
% 2.25/1.01  --eq_ax_congr_red                       true
% 2.25/1.01  --pure_diseq_elim                       true
% 2.25/1.01  --brand_transform                       false
% 2.25/1.01  --non_eq_to_eq                          false
% 2.25/1.01  --prep_def_merge                        true
% 2.25/1.01  --prep_def_merge_prop_impl              false
% 2.25/1.01  --prep_def_merge_mbd                    true
% 2.25/1.01  --prep_def_merge_tr_red                 false
% 2.25/1.01  --prep_def_merge_tr_cl                  false
% 2.25/1.01  --smt_preprocessing                     true
% 2.25/1.01  --smt_ac_axioms                         fast
% 2.25/1.01  --preprocessed_out                      false
% 2.25/1.01  --preprocessed_stats                    false
% 2.25/1.01  
% 2.25/1.01  ------ Abstraction refinement Options
% 2.25/1.01  
% 2.25/1.01  --abstr_ref                             []
% 2.25/1.01  --abstr_ref_prep                        false
% 2.25/1.01  --abstr_ref_until_sat                   false
% 2.25/1.01  --abstr_ref_sig_restrict                funpre
% 2.25/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/1.01  --abstr_ref_under                       []
% 2.25/1.01  
% 2.25/1.01  ------ SAT Options
% 2.25/1.01  
% 2.25/1.01  --sat_mode                              false
% 2.25/1.01  --sat_fm_restart_options                ""
% 2.25/1.01  --sat_gr_def                            false
% 2.25/1.01  --sat_epr_types                         true
% 2.25/1.01  --sat_non_cyclic_types                  false
% 2.25/1.01  --sat_finite_models                     false
% 2.25/1.01  --sat_fm_lemmas                         false
% 2.25/1.01  --sat_fm_prep                           false
% 2.25/1.01  --sat_fm_uc_incr                        true
% 2.25/1.01  --sat_out_model                         small
% 2.25/1.01  --sat_out_clauses                       false
% 2.25/1.01  
% 2.25/1.01  ------ QBF Options
% 2.25/1.01  
% 2.25/1.01  --qbf_mode                              false
% 2.25/1.01  --qbf_elim_univ                         false
% 2.25/1.01  --qbf_dom_inst                          none
% 2.25/1.01  --qbf_dom_pre_inst                      false
% 2.25/1.01  --qbf_sk_in                             false
% 2.25/1.01  --qbf_pred_elim                         true
% 2.25/1.01  --qbf_split                             512
% 2.25/1.01  
% 2.25/1.01  ------ BMC1 Options
% 2.25/1.01  
% 2.25/1.01  --bmc1_incremental                      false
% 2.25/1.01  --bmc1_axioms                           reachable_all
% 2.25/1.01  --bmc1_min_bound                        0
% 2.25/1.01  --bmc1_max_bound                        -1
% 2.25/1.01  --bmc1_max_bound_default                -1
% 2.25/1.01  --bmc1_symbol_reachability              true
% 2.25/1.01  --bmc1_property_lemmas                  false
% 2.25/1.01  --bmc1_k_induction                      false
% 2.25/1.01  --bmc1_non_equiv_states                 false
% 2.25/1.01  --bmc1_deadlock                         false
% 2.25/1.01  --bmc1_ucm                              false
% 2.25/1.01  --bmc1_add_unsat_core                   none
% 2.25/1.01  --bmc1_unsat_core_children              false
% 2.25/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/1.01  --bmc1_out_stat                         full
% 2.25/1.01  --bmc1_ground_init                      false
% 2.25/1.01  --bmc1_pre_inst_next_state              false
% 2.25/1.01  --bmc1_pre_inst_state                   false
% 2.25/1.01  --bmc1_pre_inst_reach_state             false
% 2.25/1.01  --bmc1_out_unsat_core                   false
% 2.25/1.01  --bmc1_aig_witness_out                  false
% 2.25/1.01  --bmc1_verbose                          false
% 2.25/1.01  --bmc1_dump_clauses_tptp                false
% 2.25/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.25/1.01  --bmc1_dump_file                        -
% 2.25/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.25/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.25/1.01  --bmc1_ucm_extend_mode                  1
% 2.25/1.01  --bmc1_ucm_init_mode                    2
% 2.25/1.01  --bmc1_ucm_cone_mode                    none
% 2.25/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.25/1.01  --bmc1_ucm_relax_model                  4
% 2.25/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.25/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/1.01  --bmc1_ucm_layered_model                none
% 2.25/1.01  --bmc1_ucm_max_lemma_size               10
% 2.25/1.01  
% 2.25/1.01  ------ AIG Options
% 2.25/1.01  
% 2.25/1.01  --aig_mode                              false
% 2.25/1.01  
% 2.25/1.01  ------ Instantiation Options
% 2.25/1.01  
% 2.25/1.01  --instantiation_flag                    true
% 2.25/1.01  --inst_sos_flag                         false
% 2.25/1.01  --inst_sos_phase                        true
% 2.25/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/1.01  --inst_lit_sel_side                     none
% 2.25/1.01  --inst_solver_per_active                1400
% 2.25/1.01  --inst_solver_calls_frac                1.
% 2.25/1.01  --inst_passive_queue_type               priority_queues
% 2.25/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/1.01  --inst_passive_queues_freq              [25;2]
% 2.25/1.01  --inst_dismatching                      true
% 2.25/1.01  --inst_eager_unprocessed_to_passive     true
% 2.25/1.01  --inst_prop_sim_given                   true
% 2.25/1.01  --inst_prop_sim_new                     false
% 2.25/1.01  --inst_subs_new                         false
% 2.25/1.01  --inst_eq_res_simp                      false
% 2.25/1.01  --inst_subs_given                       false
% 2.25/1.01  --inst_orphan_elimination               true
% 2.25/1.01  --inst_learning_loop_flag               true
% 2.25/1.01  --inst_learning_start                   3000
% 2.25/1.01  --inst_learning_factor                  2
% 2.25/1.01  --inst_start_prop_sim_after_learn       3
% 2.25/1.01  --inst_sel_renew                        solver
% 2.25/1.01  --inst_lit_activity_flag                true
% 2.25/1.01  --inst_restr_to_given                   false
% 2.25/1.01  --inst_activity_threshold               500
% 2.25/1.01  --inst_out_proof                        true
% 2.25/1.01  
% 2.25/1.01  ------ Resolution Options
% 2.25/1.01  
% 2.25/1.01  --resolution_flag                       false
% 2.25/1.01  --res_lit_sel                           adaptive
% 2.25/1.01  --res_lit_sel_side                      none
% 2.25/1.01  --res_ordering                          kbo
% 2.25/1.01  --res_to_prop_solver                    active
% 2.25/1.01  --res_prop_simpl_new                    false
% 2.25/1.01  --res_prop_simpl_given                  true
% 2.25/1.01  --res_passive_queue_type                priority_queues
% 2.25/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/1.01  --res_passive_queues_freq               [15;5]
% 2.25/1.01  --res_forward_subs                      full
% 2.25/1.01  --res_backward_subs                     full
% 2.25/1.01  --res_forward_subs_resolution           true
% 2.25/1.01  --res_backward_subs_resolution          true
% 2.25/1.01  --res_orphan_elimination                true
% 2.25/1.01  --res_time_limit                        2.
% 2.25/1.01  --res_out_proof                         true
% 2.25/1.01  
% 2.25/1.01  ------ Superposition Options
% 2.25/1.01  
% 2.25/1.01  --superposition_flag                    true
% 2.25/1.01  --sup_passive_queue_type                priority_queues
% 2.25/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.25/1.01  --demod_completeness_check              fast
% 2.25/1.01  --demod_use_ground                      true
% 2.25/1.01  --sup_to_prop_solver                    passive
% 2.25/1.01  --sup_prop_simpl_new                    true
% 2.25/1.01  --sup_prop_simpl_given                  true
% 2.25/1.01  --sup_fun_splitting                     false
% 2.25/1.01  --sup_smt_interval                      50000
% 2.25/1.01  
% 2.25/1.01  ------ Superposition Simplification Setup
% 2.25/1.01  
% 2.25/1.01  --sup_indices_passive                   []
% 2.25/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/1.01  --sup_full_bw                           [BwDemod]
% 2.25/1.01  --sup_immed_triv                        [TrivRules]
% 2.25/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/1.01  --sup_immed_bw_main                     []
% 2.25/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/1.01  
% 2.25/1.01  ------ Combination Options
% 2.25/1.01  
% 2.25/1.01  --comb_res_mult                         3
% 2.25/1.01  --comb_sup_mult                         2
% 2.25/1.01  --comb_inst_mult                        10
% 2.25/1.01  
% 2.25/1.01  ------ Debug Options
% 2.25/1.01  
% 2.25/1.01  --dbg_backtrace                         false
% 2.25/1.01  --dbg_dump_prop_clauses                 false
% 2.25/1.01  --dbg_dump_prop_clauses_file            -
% 2.25/1.01  --dbg_out_stat                          false
% 2.25/1.01  
% 2.25/1.01  
% 2.25/1.01  
% 2.25/1.01  
% 2.25/1.01  ------ Proving...
% 2.25/1.01  
% 2.25/1.01  
% 2.25/1.01  % SZS status Theorem for theBenchmark.p
% 2.25/1.01  
% 2.25/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.25/1.01  
% 2.25/1.01  fof(f7,conjecture,(
% 2.25/1.01    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 2.25/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/1.01  
% 2.25/1.01  fof(f8,negated_conjecture,(
% 2.25/1.01    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 2.25/1.01    inference(negated_conjecture,[],[f7])).
% 2.25/1.01  
% 2.25/1.01  fof(f21,plain,(
% 2.25/1.01    ? [X0] : (? [X1] : (? [X2] : ((k12_lattice3(X0,X1,X2) = X1 <~> r3_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 2.25/1.01    inference(ennf_transformation,[],[f8])).
% 2.25/1.01  
% 2.25/1.01  fof(f22,plain,(
% 2.25/1.01    ? [X0] : (? [X1] : (? [X2] : ((k12_lattice3(X0,X1,X2) = X1 <~> r3_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 2.25/1.01    inference(flattening,[],[f21])).
% 2.25/1.01  
% 2.25/1.01  fof(f29,plain,(
% 2.25/1.01    ? [X0] : (? [X1] : (? [X2] : (((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 2.25/1.01    inference(nnf_transformation,[],[f22])).
% 2.25/1.01  
% 2.25/1.01  fof(f30,plain,(
% 2.25/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 2.25/1.01    inference(flattening,[],[f29])).
% 2.25/1.01  
% 2.25/1.01  fof(f33,plain,(
% 2.25/1.01    ( ! [X0,X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r3_orders_2(X0,X1,sK3) | k12_lattice3(X0,X1,sK3) != X1) & (r3_orders_2(X0,X1,sK3) | k12_lattice3(X0,X1,sK3) = X1) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.25/1.01    introduced(choice_axiom,[])).
% 2.25/1.01  
% 2.25/1.01  fof(f32,plain,(
% 2.25/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_orders_2(X0,sK2,X2) | k12_lattice3(X0,sK2,X2) != sK2) & (r3_orders_2(X0,sK2,X2) | k12_lattice3(X0,sK2,X2) = sK2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.25/1.01    introduced(choice_axiom,[])).
% 2.25/1.01  
% 2.25/1.01  fof(f31,plain,(
% 2.25/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : ((~r3_orders_2(sK1,X1,X2) | k12_lattice3(sK1,X1,X2) != X1) & (r3_orders_2(sK1,X1,X2) | k12_lattice3(sK1,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v2_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1))),
% 2.25/1.01    introduced(choice_axiom,[])).
% 2.25/1.01  
% 2.25/1.01  fof(f34,plain,(
% 2.25/1.01    (((~r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2) & (r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v2_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1)),
% 2.25/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).
% 2.25/1.01  
% 2.25/1.01  fof(f53,plain,(
% 2.25/1.01    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.25/1.01    inference(cnf_transformation,[],[f34])).
% 2.25/1.01  
% 2.25/1.01  fof(f52,plain,(
% 2.25/1.01    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.25/1.01    inference(cnf_transformation,[],[f34])).
% 2.25/1.01  
% 2.25/1.01  fof(f5,axiom,(
% 2.25/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 2.25/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/1.01  
% 2.25/1.01  fof(f17,plain,(
% 2.25/1.01    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.25/1.01    inference(ennf_transformation,[],[f5])).
% 2.25/1.01  
% 2.25/1.01  fof(f18,plain,(
% 2.25/1.01    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.25/1.01    inference(flattening,[],[f17])).
% 2.25/1.01  
% 2.25/1.01  fof(f46,plain,(
% 2.25/1.01    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.25/1.01    inference(cnf_transformation,[],[f18])).
% 2.25/1.01  
% 2.25/1.01  fof(f51,plain,(
% 2.25/1.01    l1_orders_2(sK1)),
% 2.25/1.01    inference(cnf_transformation,[],[f34])).
% 2.25/1.01  
% 2.25/1.01  fof(f49,plain,(
% 2.25/1.01    v5_orders_2(sK1)),
% 2.25/1.01    inference(cnf_transformation,[],[f34])).
% 2.25/1.01  
% 2.25/1.01  fof(f50,plain,(
% 2.25/1.01    v2_lattice3(sK1)),
% 2.25/1.01    inference(cnf_transformation,[],[f34])).
% 2.25/1.01  
% 2.25/1.01  fof(f54,plain,(
% 2.25/1.01    r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2),
% 2.25/1.01    inference(cnf_transformation,[],[f34])).
% 2.25/1.01  
% 2.25/1.01  fof(f1,axiom,(
% 2.25/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.25/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/1.01  
% 2.25/1.01  fof(f9,plain,(
% 2.25/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.25/1.01    inference(ennf_transformation,[],[f1])).
% 2.25/1.01  
% 2.25/1.01  fof(f10,plain,(
% 2.25/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.25/1.01    inference(flattening,[],[f9])).
% 2.25/1.01  
% 2.25/1.01  fof(f23,plain,(
% 2.25/1.01    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.25/1.01    inference(nnf_transformation,[],[f10])).
% 2.25/1.01  
% 2.25/1.01  fof(f35,plain,(
% 2.25/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.25/1.01    inference(cnf_transformation,[],[f23])).
% 2.25/1.01  
% 2.25/1.01  fof(f48,plain,(
% 2.25/1.01    v3_orders_2(sK1)),
% 2.25/1.01    inference(cnf_transformation,[],[f34])).
% 2.25/1.01  
% 2.25/1.01  fof(f3,axiom,(
% 2.25/1.01    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.25/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/1.01  
% 2.25/1.01  fof(f13,plain,(
% 2.25/1.01    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.25/1.01    inference(ennf_transformation,[],[f3])).
% 2.25/1.01  
% 2.25/1.01  fof(f14,plain,(
% 2.25/1.01    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.25/1.01    inference(flattening,[],[f13])).
% 2.25/1.01  
% 2.25/1.01  fof(f38,plain,(
% 2.25/1.01    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.25/1.01    inference(cnf_transformation,[],[f14])).
% 2.25/1.01  
% 2.25/1.01  fof(f2,axiom,(
% 2.25/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 2.25/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/1.01  
% 2.25/1.01  fof(f11,plain,(
% 2.25/1.01    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.25/1.01    inference(ennf_transformation,[],[f2])).
% 2.25/1.01  
% 2.25/1.01  fof(f12,plain,(
% 2.25/1.01    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.25/1.01    inference(flattening,[],[f11])).
% 2.25/1.01  
% 2.25/1.01  fof(f37,plain,(
% 2.25/1.01    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.25/1.01    inference(cnf_transformation,[],[f12])).
% 2.25/1.01  
% 2.25/1.01  fof(f4,axiom,(
% 2.25/1.01    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.25/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/1.01  
% 2.25/1.01  fof(f15,plain,(
% 2.25/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.25/1.01    inference(ennf_transformation,[],[f4])).
% 2.25/1.01  
% 2.25/1.01  fof(f16,plain,(
% 2.25/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.25/1.01    inference(flattening,[],[f15])).
% 2.25/1.01  
% 2.25/1.01  fof(f24,plain,(
% 2.25/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.25/1.01    inference(nnf_transformation,[],[f16])).
% 2.25/1.01  
% 2.25/1.01  fof(f25,plain,(
% 2.25/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.25/1.01    inference(flattening,[],[f24])).
% 2.25/1.01  
% 2.25/1.01  fof(f26,plain,(
% 2.25/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.25/1.01    inference(rectify,[],[f25])).
% 2.25/1.01  
% 2.25/1.01  fof(f27,plain,(
% 2.25/1.01    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.25/1.01    introduced(choice_axiom,[])).
% 2.25/1.01  
% 2.25/1.01  fof(f28,plain,(
% 2.25/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.25/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.25/1.01  
% 2.25/1.01  fof(f43,plain,(
% 2.25/1.01    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.25/1.01    inference(cnf_transformation,[],[f28])).
% 2.25/1.01  
% 2.25/1.01  fof(f45,plain,(
% 2.25/1.01    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.25/1.01    inference(cnf_transformation,[],[f28])).
% 2.25/1.01  
% 2.25/1.01  fof(f40,plain,(
% 2.25/1.01    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.25/1.01    inference(cnf_transformation,[],[f28])).
% 2.25/1.01  
% 2.25/1.01  fof(f57,plain,(
% 2.25/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.25/1.01    inference(equality_resolution,[],[f40])).
% 2.25/1.01  
% 2.25/1.01  fof(f55,plain,(
% 2.25/1.01    ~r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2),
% 2.25/1.01    inference(cnf_transformation,[],[f34])).
% 2.25/1.01  
% 2.25/1.01  fof(f36,plain,(
% 2.25/1.01    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.25/1.01    inference(cnf_transformation,[],[f23])).
% 2.25/1.01  
% 2.25/1.01  cnf(c_15,negated_conjecture,
% 2.25/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_928,negated_conjecture,
% 2.25/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1334,plain,
% 2.25/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.25/1.01      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_16,negated_conjecture,
% 2.25/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_927,negated_conjecture,
% 2.25/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1335,plain,
% 2.25/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.25/1.01      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_11,plain,
% 2.25/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.25/1.01      | ~ v5_orders_2(X1)
% 2.25/1.01      | ~ v2_lattice3(X1)
% 2.25/1.01      | ~ l1_orders_2(X1)
% 2.25/1.01      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 2.25/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_17,negated_conjecture,
% 2.25/1.01      ( l1_orders_2(sK1) ),
% 2.25/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_700,plain,
% 2.25/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.25/1.01      | ~ v5_orders_2(X1)
% 2.25/1.01      | ~ v2_lattice3(X1)
% 2.25/1.01      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 2.25/1.01      | sK1 != X1 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_701,plain,
% 2.25/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ v5_orders_2(sK1)
% 2.25/1.01      | ~ v2_lattice3(sK1)
% 2.25/1.01      | k12_lattice3(sK1,X0,X1) = k11_lattice3(sK1,X0,X1) ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_700]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_19,negated_conjecture,
% 2.25/1.01      ( v5_orders_2(sK1) ),
% 2.25/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_18,negated_conjecture,
% 2.25/1.01      ( v2_lattice3(sK1) ),
% 2.25/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_705,plain,
% 2.25/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | k12_lattice3(sK1,X0,X1) = k11_lattice3(sK1,X0,X1) ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_701,c_19,c_18]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_706,plain,
% 2.25/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | k12_lattice3(sK1,X1,X0) = k11_lattice3(sK1,X1,X0) ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_705]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_915,plain,
% 2.25/1.01      ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 2.25/1.01      | k12_lattice3(sK1,X1_44,X0_44) = k11_lattice3(sK1,X1_44,X0_44) ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_706]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1349,plain,
% 2.25/1.01      ( k12_lattice3(sK1,X0_44,X1_44) = k11_lattice3(sK1,X0_44,X1_44)
% 2.25/1.01      | m1_subset_1(X1_44,u1_struct_0(sK1)) != iProver_top
% 2.25/1.01      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top ),
% 2.25/1.01      inference(predicate_to_equality,[status(thm)],[c_915]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1639,plain,
% 2.25/1.01      ( k12_lattice3(sK1,sK2,X0_44) = k11_lattice3(sK1,sK2,X0_44)
% 2.25/1.01      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top ),
% 2.25/1.01      inference(superposition,[status(thm)],[c_1335,c_1349]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1767,plain,
% 2.25/1.01      ( k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
% 2.25/1.01      inference(superposition,[status(thm)],[c_1334,c_1639]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_14,negated_conjecture,
% 2.25/1.01      ( r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_190,plain,
% 2.25/1.01      ( r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(prop_impl,[status(thm)],[c_14]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1,plain,
% 2.25/1.01      ( r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ r3_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ v3_orders_2(X0)
% 2.25/1.01      | ~ l1_orders_2(X0) ),
% 2.25/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_20,negated_conjecture,
% 2.25/1.01      ( v3_orders_2(sK1) ),
% 2.25/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_332,plain,
% 2.25/1.01      ( r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ r3_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | sK1 != X0 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_333,plain,
% 2.25/1.01      ( r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r3_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | v2_struct_0(sK1)
% 2.25/1.01      | ~ l1_orders_2(sK1) ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_332]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_3,plain,
% 2.25/1.01      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.25/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_53,plain,
% 2.25/1.01      ( ~ v2_lattice3(sK1) | ~ v2_struct_0(sK1) | ~ l1_orders_2(sK1) ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_337,plain,
% 2.25/1.01      ( r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r3_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_333,c_18,c_17,c_53]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_338,plain,
% 2.25/1.01      ( r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r3_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_337]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_417,plain,
% 2.25/1.01      ( r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | k12_lattice3(sK1,sK2,sK3) = sK2
% 2.25/1.01      | sK3 != X1
% 2.25/1.01      | sK2 != X0
% 2.25/1.01      | sK1 != sK1 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_190,c_338]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_418,plain,
% 2.25/1.01      ( r1_orders_2(sK1,sK2,sK3)
% 2.25/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.25/1.01      | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_417]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_420,plain,
% 2.25/1.01      ( r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_418,c_16,c_15]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_828,plain,
% 2.25/1.01      ( r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(prop_impl,[status(thm)],[c_16,c_15,c_418]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_926,plain,
% 2.25/1.01      ( r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_828]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1336,plain,
% 2.25/1.01      ( k12_lattice3(sK1,sK2,sK3) = sK2
% 2.25/1.01      | r1_orders_2(sK1,sK2,sK3) = iProver_top ),
% 2.25/1.01      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_934,plain,( X0_44 = X0_44 ),theory(equality) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_943,plain,
% 2.25/1.01      ( sK2 = sK2 ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_934]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_2,plain,
% 2.25/1.01      ( r3_orders_2(X0,X1,X1)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ v3_orders_2(X0)
% 2.25/1.01      | ~ l1_orders_2(X0) ),
% 2.25/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_311,plain,
% 2.25/1.01      ( r3_orders_2(X0,X1,X1)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | sK1 != X0 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_312,plain,
% 2.25/1.01      ( r3_orders_2(sK1,X0,X0)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | v2_struct_0(sK1)
% 2.25/1.01      | ~ l1_orders_2(sK1) ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_311]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_316,plain,
% 2.25/1.01      ( r3_orders_2(sK1,X0,X0)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_312,c_18,c_17,c_53]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_317,plain,
% 2.25/1.01      ( r3_orders_2(sK1,X0,X0)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_316]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_445,plain,
% 2.25/1.01      ( r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | X1 != X3
% 2.25/1.01      | X0 != X3
% 2.25/1.01      | sK1 != sK1 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_317,c_338]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_446,plain,
% 2.25/1.01      ( r1_orders_2(sK1,X0,X0)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_445]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_924,plain,
% 2.25/1.01      ( r1_orders_2(sK1,X0_44,X0_44)
% 2.25/1.01      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1_44,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_446]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_931,plain,
% 2.25/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 2.25/1.01      inference(splitting,
% 2.25/1.01                [splitting(split),new_symbols(definition,[])],
% 2.25/1.01                [c_924]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_930,plain,
% 2.25/1.01      ( r1_orders_2(sK1,X0_44,X0_44)
% 2.25/1.01      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ sP1_iProver_split ),
% 2.25/1.01      inference(splitting,
% 2.25/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.25/1.01                [c_924]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_950,plain,
% 2.25/1.01      ( r1_orders_2(sK1,sK2,sK2)
% 2.25/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.25/1.01      | ~ sP1_iProver_split ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_930]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_929,plain,
% 2.25/1.01      ( ~ m1_subset_1(X0_44,u1_struct_0(sK1)) | ~ sP0_iProver_split ),
% 2.25/1.01      inference(splitting,
% 2.25/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.25/1.01                [c_924]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_953,plain,
% 2.25/1.01      ( ~ m1_subset_1(sK2,u1_struct_0(sK1)) | ~ sP0_iProver_split ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_929]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_935,plain,
% 2.25/1.01      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 2.25/1.01      theory(equality) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1520,plain,
% 2.25/1.01      ( k12_lattice3(sK1,sK2,sK3) != X0_44
% 2.25/1.01      | k12_lattice3(sK1,sK2,sK3) = sK2
% 2.25/1.01      | sK2 != X0_44 ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_935]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1568,plain,
% 2.25/1.01      ( k12_lattice3(sK1,sK2,sK3) != k11_lattice3(sK1,sK2,sK3)
% 2.25/1.01      | k12_lattice3(sK1,sK2,sK3) = sK2
% 2.25/1.01      | sK2 != k11_lattice3(sK1,sK2,sK3) ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_1520]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1569,plain,
% 2.25/1.01      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.25/1.01      | k12_lattice3(sK1,sK2,sK3) = k11_lattice3(sK1,sK2,sK3) ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_915]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1579,plain,
% 2.25/1.01      ( k11_lattice3(sK1,sK2,sK3) != X0_44
% 2.25/1.01      | sK2 != X0_44
% 2.25/1.01      | sK2 = k11_lattice3(sK1,sK2,sK3) ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_935]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1580,plain,
% 2.25/1.01      ( k11_lattice3(sK1,sK2,sK3) != sK2
% 2.25/1.01      | sK2 = k11_lattice3(sK1,sK2,sK3)
% 2.25/1.01      | sK2 != sK2 ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_1579]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_6,plain,
% 2.25/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X3)
% 2.25/1.01      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.25/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_143,plain,
% 2.25/1.01      ( ~ v2_lattice3(X0)
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X3)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.25/1.01      inference(global_propositional_subsumption,[status(thm)],[c_6,c_3]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_144,plain,
% 2.25/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X3)
% 2.25/1.01      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_143]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_540,plain,
% 2.25/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X3)
% 2.25/1.01      | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | k11_lattice3(X0,X3,X2) = X1
% 2.25/1.01      | sK1 != X0 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_144,c_17]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_541,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 2.25/1.01      | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.25/1.01      | ~ v5_orders_2(sK1)
% 2.25/1.01      | ~ v2_lattice3(sK1)
% 2.25/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_540]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_543,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 2.25/1.01      | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_541,c_19,c_18]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_544,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 2.25/1.01      | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_543]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_921,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0_44,X1_44)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0_44,X2_44)
% 2.25/1.01      | r1_orders_2(sK1,sK0(sK1,X2_44,X1_44,X0_44),X2_44)
% 2.25/1.01      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X2_44,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,X2_44,X1_44) = X0_44 ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_544]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1614,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0_44,sK3)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0_44,sK2)
% 2.25/1.01      | r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_44),sK2)
% 2.25/1.01      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,sK2,sK3) = X0_44 ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_921]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1621,plain,
% 2.25/1.01      ( r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK2,sK3)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK2,sK2)
% 2.25/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_1614]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_4,plain,
% 2.25/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X3)
% 2.25/1.01      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.25/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_155,plain,
% 2.25/1.01      ( ~ v2_lattice3(X0)
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X3)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.25/1.01      inference(global_propositional_subsumption,[status(thm)],[c_4,c_3]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_156,plain,
% 2.25/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X3)
% 2.25/1.01      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_155]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_474,plain,
% 2.25/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ r1_orders_2(X0,X1,X3)
% 2.25/1.01      | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | k11_lattice3(X0,X3,X2) = X1
% 2.25/1.01      | sK1 != X0 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_156,c_17]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_475,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.25/1.01      | ~ v5_orders_2(sK1)
% 2.25/1.01      | ~ v2_lattice3(sK1)
% 2.25/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_474]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_479,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_475,c_19,c_18]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_480,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0,X2)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,X2,X1) = X0 ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_479]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_923,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0_44,X1_44)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0_44,X2_44)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK0(sK1,X2_44,X1_44,X0_44),X0_44)
% 2.25/1.01      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X2_44,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,X2_44,X1_44) = X0_44 ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_480]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1612,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0_44,sK3)
% 2.25/1.01      | ~ r1_orders_2(sK1,X0_44,sK2)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,X0_44),X0_44)
% 2.25/1.01      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,sK2,sK3) = X0_44 ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_923]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1629,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK2,sK3)
% 2.25/1.01      | ~ r1_orders_2(sK1,sK2,sK2)
% 2.25/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.25/1.01      | k11_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(instantiation,[status(thm)],[c_1612]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1736,plain,
% 2.25/1.01      ( k12_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_1336,c_16,c_15,c_943,c_926,c_931,c_950,c_953,c_1568,
% 2.25/1.01                 c_1569,c_1580,c_1621,c_1629]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1772,plain,
% 2.25/1.01      ( k11_lattice3(sK1,sK2,sK3) = sK2 ),
% 2.25/1.01      inference(light_normalisation,[status(thm)],[c_1767,c_1736]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_9,plain,
% 2.25/1.01      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ l1_orders_2(X0) ),
% 2.25/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_124,plain,
% 2.25/1.01      ( ~ v2_lattice3(X0)
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.25/1.01      | ~ l1_orders_2(X0) ),
% 2.25/1.01      inference(global_propositional_subsumption,[status(thm)],[c_9,c_3]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_125,plain,
% 2.25/1.01      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | ~ l1_orders_2(X0) ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_124]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_635,plain,
% 2.25/1.01      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.25/1.01      | ~ v5_orders_2(X0)
% 2.25/1.01      | ~ v2_lattice3(X0)
% 2.25/1.01      | sK1 != X0 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_125,c_17]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_636,plain,
% 2.25/1.01      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1))
% 2.25/1.01      | ~ v5_orders_2(sK1)
% 2.25/1.01      | ~ v2_lattice3(sK1) ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_635]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_640,plain,
% 2.25/1.01      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_636,c_19,c_18]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_641,plain,
% 2.25/1.01      ( r1_orders_2(sK1,k11_lattice3(sK1,X0,X1),X1)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(k11_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_640]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_918,plain,
% 2.25/1.01      ( r1_orders_2(sK1,k11_lattice3(sK1,X0_44,X1_44),X1_44)
% 2.25/1.01      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(k11_lattice3(sK1,X0_44,X1_44),u1_struct_0(sK1)) ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_641]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_1346,plain,
% 2.25/1.01      ( r1_orders_2(sK1,k11_lattice3(sK1,X0_44,X1_44),X1_44) = iProver_top
% 2.25/1.01      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 2.25/1.01      | m1_subset_1(X1_44,u1_struct_0(sK1)) != iProver_top
% 2.25/1.01      | m1_subset_1(k11_lattice3(sK1,X0_44,X1_44),u1_struct_0(sK1)) != iProver_top ),
% 2.25/1.01      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_2211,plain,
% 2.25/1.01      ( r1_orders_2(sK1,k11_lattice3(sK1,sK2,sK3),sK3) = iProver_top
% 2.25/1.01      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.25/1.01      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.25/1.01      inference(superposition,[status(thm)],[c_1772,c_1346]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_2223,plain,
% 2.25/1.01      ( r1_orders_2(sK1,sK2,sK3) = iProver_top
% 2.25/1.01      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.25/1.01      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.25/1.01      inference(light_normalisation,[status(thm)],[c_2211,c_1772]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_13,negated_conjecture,
% 2.25/1.01      ( ~ r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 2.25/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_188,plain,
% 2.25/1.01      ( ~ r3_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 2.25/1.01      inference(prop_impl,[status(thm)],[c_13]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_0,plain,
% 2.25/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | r3_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ v3_orders_2(X0)
% 2.25/1.01      | ~ l1_orders_2(X0) ),
% 2.25/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_356,plain,
% 2.25/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.25/1.01      | r3_orders_2(X0,X1,X2)
% 2.25/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/1.01      | v2_struct_0(X0)
% 2.25/1.01      | ~ l1_orders_2(X0)
% 2.25/1.01      | sK1 != X0 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_357,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | r3_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | v2_struct_0(sK1)
% 2.25/1.01      | ~ l1_orders_2(sK1) ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_356]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_361,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | r3_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_357,c_18,c_17,c_53]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_362,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | r3_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.25/1.01      inference(renaming,[status(thm)],[c_361]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_431,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,X0,X1)
% 2.25/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.25/1.01      | k12_lattice3(sK1,sK2,sK3) != sK2
% 2.25/1.01      | sK3 != X1
% 2.25/1.01      | sK2 != X0
% 2.25/1.01      | sK1 != sK1 ),
% 2.25/1.01      inference(resolution_lifted,[status(thm)],[c_188,c_362]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_432,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,sK2,sK3)
% 2.25/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.25/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.25/1.01      | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 2.25/1.01      inference(unflattening,[status(thm)],[c_431]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_434,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 2.25/1.01      inference(global_propositional_subsumption,
% 2.25/1.01                [status(thm)],
% 2.25/1.01                [c_432,c_16,c_15]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_826,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 2.25/1.01      inference(prop_impl,[status(thm)],[c_16,c_15,c_432]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_925,plain,
% 2.25/1.01      ( ~ r1_orders_2(sK1,sK2,sK3) | k12_lattice3(sK1,sK2,sK3) != sK2 ),
% 2.25/1.01      inference(subtyping,[status(esa)],[c_826]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_947,plain,
% 2.25/1.01      ( k12_lattice3(sK1,sK2,sK3) != sK2
% 2.25/1.01      | r1_orders_2(sK1,sK2,sK3) != iProver_top ),
% 2.25/1.01      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_26,plain,
% 2.25/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.25/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(c_25,plain,
% 2.25/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.25/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.25/1.01  
% 2.25/1.01  cnf(contradiction,plain,
% 2.25/1.01      ( $false ),
% 2.25/1.01      inference(minisat,[status(thm)],[c_2223,c_1736,c_947,c_26,c_25]) ).
% 2.25/1.01  
% 2.25/1.01  
% 2.25/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.25/1.01  
% 2.25/1.01  ------                               Statistics
% 2.25/1.01  
% 2.25/1.01  ------ General
% 2.25/1.01  
% 2.25/1.01  abstr_ref_over_cycles:                  0
% 2.25/1.01  abstr_ref_under_cycles:                 0
% 2.25/1.01  gc_basic_clause_elim:                   0
% 2.25/1.01  forced_gc_time:                         0
% 2.25/1.01  parsing_time:                           0.024
% 2.25/1.01  unif_index_cands_time:                  0.
% 2.25/1.01  unif_index_add_time:                    0.
% 2.25/1.01  orderings_time:                         0.
% 2.25/1.01  out_proof_time:                         0.019
% 2.25/1.01  total_time:                             0.145
% 2.25/1.01  num_of_symbols:                         48
% 2.25/1.01  num_of_terms:                           1448
% 2.25/1.01  
% 2.25/1.01  ------ Preprocessing
% 2.25/1.01  
% 2.25/1.01  num_of_splits:                          3
% 2.25/1.01  num_of_split_atoms:                     2
% 2.25/1.01  num_of_reused_defs:                     1
% 2.25/1.01  num_eq_ax_congr_red:                    25
% 2.25/1.01  num_of_sem_filtered_clauses:            3
% 2.25/1.01  num_of_subtypes:                        3
% 2.25/1.01  monotx_restored_types:                  0
% 2.25/1.01  sat_num_of_epr_types:                   0
% 2.25/1.01  sat_num_of_non_cyclic_types:            0
% 2.25/1.01  sat_guarded_non_collapsed_types:        1
% 2.25/1.01  num_pure_diseq_elim:                    0
% 2.25/1.01  simp_replaced_by:                       0
% 2.25/1.01  res_preprocessed:                       79
% 2.25/1.01  prep_upred:                             0
% 2.25/1.01  prep_unflattend:                        19
% 2.25/1.01  smt_new_axioms:                         0
% 2.25/1.01  pred_elim_cands:                        2
% 2.25/1.01  pred_elim:                              6
% 2.25/1.01  pred_elim_cl:                           6
% 2.25/1.01  pred_elim_cycles:                       8
% 2.25/1.01  merged_defs:                            8
% 2.25/1.01  merged_defs_ncl:                        0
% 2.25/1.01  bin_hyper_res:                          9
% 2.25/1.01  prep_cycles:                            4
% 2.25/1.01  pred_elim_time:                         0.015
% 2.25/1.01  splitting_time:                         0.
% 2.25/1.01  sem_filter_time:                        0.
% 2.25/1.01  monotx_time:                            0.
% 2.25/1.01  subtype_inf_time:                       0.
% 2.25/1.01  
% 2.25/1.01  ------ Problem properties
% 2.25/1.01  
% 2.25/1.01  clauses:                                18
% 2.25/1.01  conjectures:                            2
% 2.25/1.01  epr:                                    2
% 2.25/1.01  horn:                                   12
% 2.25/1.01  ground:                                 6
% 2.25/1.01  unary:                                  2
% 2.25/1.01  binary:                                 5
% 2.25/1.01  lits:                                   67
% 2.25/1.01  lits_eq:                                9
% 2.25/1.01  fd_pure:                                0
% 2.25/1.01  fd_pseudo:                              0
% 2.25/1.01  fd_cond:                                0
% 2.25/1.01  fd_pseudo_cond:                         4
% 2.25/1.01  ac_symbols:                             0
% 2.25/1.01  
% 2.25/1.01  ------ Propositional Solver
% 2.25/1.01  
% 2.25/1.01  prop_solver_calls:                      27
% 2.25/1.01  prop_fast_solver_calls:                 957
% 2.25/1.01  smt_solver_calls:                       0
% 2.25/1.01  smt_fast_solver_calls:                  0
% 2.25/1.01  prop_num_of_clauses:                    526
% 2.25/1.01  prop_preprocess_simplified:             2608
% 2.25/1.01  prop_fo_subsumed:                       43
% 2.25/1.01  prop_solver_time:                       0.
% 2.25/1.01  smt_solver_time:                        0.
% 2.25/1.01  smt_fast_solver_time:                   0.
% 2.25/1.01  prop_fast_solver_time:                  0.
% 2.25/1.01  prop_unsat_core_time:                   0.
% 2.25/1.01  
% 2.25/1.01  ------ QBF
% 2.25/1.01  
% 2.25/1.01  qbf_q_res:                              0
% 2.25/1.01  qbf_num_tautologies:                    0
% 2.25/1.01  qbf_prep_cycles:                        0
% 2.25/1.01  
% 2.25/1.01  ------ BMC1
% 2.25/1.01  
% 2.25/1.01  bmc1_current_bound:                     -1
% 2.25/1.01  bmc1_last_solved_bound:                 -1
% 2.25/1.01  bmc1_unsat_core_size:                   -1
% 2.25/1.01  bmc1_unsat_core_parents_size:           -1
% 2.25/1.01  bmc1_merge_next_fun:                    0
% 2.25/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.25/1.01  
% 2.25/1.01  ------ Instantiation
% 2.25/1.01  
% 2.25/1.01  inst_num_of_clauses:                    126
% 2.25/1.01  inst_num_in_passive:                    11
% 2.25/1.01  inst_num_in_active:                     89
% 2.25/1.01  inst_num_in_unprocessed:                26
% 2.25/1.01  inst_num_of_loops:                      110
% 2.25/1.01  inst_num_of_learning_restarts:          0
% 2.25/1.01  inst_num_moves_active_passive:          17
% 2.25/1.01  inst_lit_activity:                      0
% 2.25/1.01  inst_lit_activity_moves:                0
% 2.25/1.01  inst_num_tautologies:                   0
% 2.25/1.01  inst_num_prop_implied:                  0
% 2.25/1.01  inst_num_existing_simplified:           0
% 2.25/1.01  inst_num_eq_res_simplified:             0
% 2.25/1.01  inst_num_child_elim:                    0
% 2.25/1.01  inst_num_of_dismatching_blockings:      12
% 2.25/1.01  inst_num_of_non_proper_insts:           91
% 2.25/1.01  inst_num_of_duplicates:                 0
% 2.25/1.01  inst_inst_num_from_inst_to_res:         0
% 2.25/1.01  inst_dismatching_checking_time:         0.
% 2.25/1.01  
% 2.25/1.01  ------ Resolution
% 2.25/1.01  
% 2.25/1.01  res_num_of_clauses:                     0
% 2.25/1.01  res_num_in_passive:                     0
% 2.25/1.01  res_num_in_active:                      0
% 2.25/1.01  res_num_of_loops:                       83
% 2.25/1.01  res_forward_subset_subsumed:            2
% 2.25/1.01  res_backward_subset_subsumed:           0
% 2.25/1.01  res_forward_subsumed:                   0
% 2.25/1.01  res_backward_subsumed:                  0
% 2.25/1.01  res_forward_subsumption_resolution:     0
% 2.25/1.01  res_backward_subsumption_resolution:    0
% 2.25/1.01  res_clause_to_clause_subsumption:       157
% 2.25/1.01  res_orphan_elimination:                 0
% 2.25/1.01  res_tautology_del:                      24
% 2.25/1.01  res_num_eq_res_simplified:              0
% 2.25/1.01  res_num_sel_changes:                    0
% 2.25/1.01  res_moves_from_active_to_pass:          0
% 2.25/1.01  
% 2.25/1.01  ------ Superposition
% 2.25/1.01  
% 2.25/1.01  sup_time_total:                         0.
% 2.25/1.01  sup_time_generating:                    0.
% 2.25/1.01  sup_time_sim_full:                      0.
% 2.25/1.01  sup_time_sim_immed:                     0.
% 2.25/1.01  
% 2.25/1.01  sup_num_of_clauses:                     36
% 2.25/1.01  sup_num_in_active:                      20
% 2.25/1.01  sup_num_in_passive:                     16
% 2.25/1.01  sup_num_of_loops:                       20
% 2.25/1.01  sup_fw_superposition:                   15
% 2.25/1.01  sup_bw_superposition:                   11
% 2.25/1.01  sup_immediate_simplified:               8
% 2.25/1.01  sup_given_eliminated:                   0
% 2.25/1.01  comparisons_done:                       0
% 2.25/1.01  comparisons_avoided:                    0
% 2.25/1.01  
% 2.25/1.01  ------ Simplifications
% 2.25/1.01  
% 2.25/1.01  
% 2.25/1.01  sim_fw_subset_subsumed:                 0
% 2.25/1.01  sim_bw_subset_subsumed:                 0
% 2.25/1.01  sim_fw_subsumed:                        2
% 2.25/1.01  sim_bw_subsumed:                        0
% 2.25/1.01  sim_fw_subsumption_res:                 0
% 2.25/1.01  sim_bw_subsumption_res:                 0
% 2.25/1.01  sim_tautology_del:                      1
% 2.25/1.01  sim_eq_tautology_del:                   2
% 2.25/1.01  sim_eq_res_simp:                        0
% 2.25/1.01  sim_fw_demodulated:                     0
% 2.25/1.01  sim_bw_demodulated:                     1
% 2.25/1.01  sim_light_normalised:                   8
% 2.25/1.01  sim_joinable_taut:                      0
% 2.25/1.01  sim_joinable_simp:                      0
% 2.25/1.01  sim_ac_normalised:                      0
% 2.25/1.01  sim_smt_subsumption:                    0
% 2.25/1.01  
%------------------------------------------------------------------------------
