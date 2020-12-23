%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1546+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:51 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 621 expanded)
%              Number of clauses        :   80 ( 146 expanded)
%              Number of leaves         :   13 ( 167 expanded)
%              Depth                    :   20
%              Number of atoms          :  673 (4974 expanded)
%              Number of equality atoms :  125 ( 935 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k13_lattice3(X0,X1,X2) = X1
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k13_lattice3(X0,X1,X2) = X1
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_orders_2(X0,X2,X1)
            | k13_lattice3(X0,X1,X2) != X1 )
          & ( r1_orders_2(X0,X2,X1)
            | k13_lattice3(X0,X1,X2) = X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_orders_2(X0,sK3,X1)
          | k13_lattice3(X0,X1,sK3) != X1 )
        & ( r1_orders_2(X0,sK3,X1)
          | k13_lattice3(X0,X1,sK3) = X1 )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r1_orders_2(X0,X2,sK2)
              | k13_lattice3(X0,sK2,X2) != sK2 )
            & ( r1_orders_2(X0,X2,sK2)
              | k13_lattice3(X0,sK2,X2) = sK2 )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X2,X1)
                  | k13_lattice3(X0,X1,X2) != X1 )
                & ( r1_orders_2(X0,X2,X1)
                  | k13_lattice3(X0,X1,X2) = X1 )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK1,X2,X1)
                | k13_lattice3(sK1,X1,X2) != X1 )
              & ( r1_orders_2(sK1,X2,X1)
                | k13_lattice3(sK1,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1)
      & v3_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r1_orders_2(sK1,sK3,sK2)
      | k13_lattice3(sK1,sK2,sK3) != sK2 )
    & ( r1_orders_2(sK1,sK3,sK2)
      | k13_lattice3(sK1,sK2,sK3) = sK2 )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1)
    & v3_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).

fof(f46,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,
    ( ~ r1_orders_2(sK1,sK3,sK2)
    | k13_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k13_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,
    ( r1_orders_2(sK1,sK3,sK2)
    | k13_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_780,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_1525,plain,
    ( k13_lattice3(sK1,X0_42,sK3) != X1_42
    | sK2 != X1_42
    | sK2 = k13_lattice3(sK1,X0_42,sK3) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_1526,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK2
    | sK2 = k13_lattice3(sK1,sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1525])).

cnf(c_782,plain,
    ( ~ m1_subset_1(X0_42,X0_43)
    | m1_subset_1(X1_42,X0_43)
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_1345,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | m1_subset_1(X1_42,u1_struct_0(sK1))
    | X1_42 != X0_42 ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_1449,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | m1_subset_1(k13_lattice3(sK1,X1_42,sK3),u1_struct_0(sK1))
    | k13_lattice3(sK1,X1_42,sK3) != X0_42 ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_1451,plain,
    ( m1_subset_1(k13_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k13_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_388,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_389,plain,
    ( r1_orders_2(sK1,X0,k13_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k13_lattice3(sK1,X1,X0),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_391,plain,
    ( r1_orders_2(sK1,X0,k13_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k13_lattice3(sK1,X1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_18,c_16])).

cnf(c_392,plain,
    ( r1_orders_2(sK1,X0,k13_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k13_lattice3(sK1,X1,X0),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_768,plain,
    ( r1_orders_2(sK1,X0_42,k13_lattice3(sK1,X1_42,X0_42))
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | ~ m1_subset_1(k13_lattice3(sK1,X1_42,X0_42),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_1393,plain,
    ( r1_orders_2(sK1,sK3,k13_lattice3(sK1,X0_42,sK3))
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ m1_subset_1(k13_lattice3(sK1,X0_42,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_1399,plain,
    ( r1_orders_2(sK1,sK3,k13_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_783,plain,
    ( ~ r1_orders_2(X0_44,X0_42,X1_42)
    | r1_orders_2(X0_44,X2_42,X3_42)
    | X2_42 != X0_42
    | X3_42 != X1_42 ),
    theory(equality)).

cnf(c_1333,plain,
    ( ~ r1_orders_2(sK1,X0_42,X1_42)
    | r1_orders_2(sK1,sK3,sK2)
    | sK2 != X1_42
    | sK3 != X0_42 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_1356,plain,
    ( ~ r1_orders_2(sK1,sK3,X0_42)
    | r1_orders_2(sK1,sK3,sK2)
    | sK2 != X0_42
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_1392,plain,
    ( ~ r1_orders_2(sK1,sK3,k13_lattice3(sK1,X0_42,sK3))
    | r1_orders_2(sK1,sK3,sK2)
    | sK2 != k13_lattice3(sK1,X0_42,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_1395,plain,
    ( ~ r1_orders_2(sK1,sK3,k13_lattice3(sK1,sK2,sK3))
    | r1_orders_2(sK1,sK3,sK2)
    | sK2 != k13_lattice3(sK1,sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_779,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_1357,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_12,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK3,sK2)
    | k13_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_774,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK3,sK2)
    | k13_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1134,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK2
    | r1_orders_2(sK1,sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_789,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK2
    | r1_orders_2(sK1,sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_4,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_261,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_262,plain,
    ( r3_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_58,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_266,plain,
    ( r3_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_262,c_17,c_16,c_58])).

cnf(c_267,plain,
    ( r3_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_282,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_283,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_287,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_283,c_17,c_16,c_58])).

cnf(c_288,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_287])).

cnf(c_345,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X0 != X3
    | X1 != X3
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_267,c_288])).

cnf(c_346,plain,
    ( r1_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_770,plain,
    ( r1_orders_2(sK1,X0_42,X0_42)
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_777,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_770])).

cnf(c_793,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_776,plain,
    ( r1_orders_2(sK1,X0_42,X0_42)
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_770])).

cnf(c_794,plain,
    ( r1_orders_2(sK1,X0_42,X0_42) = iProver_top
    | m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_796,plain,
    ( r1_orders_2(sK1,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_770])).

cnf(c_797,plain,
    ( m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_799,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k13_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_536,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k13_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_537,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k13_lattice3(sK1,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_541,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k13_lattice3(sK1,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_18,c_16])).

cnf(c_542,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k13_lattice3(sK1,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_763,plain,
    ( ~ r1_orders_2(sK1,X0_42,X1_42)
    | ~ r1_orders_2(sK1,X2_42,X1_42)
    | ~ r1_orders_2(sK1,X1_42,sK0(sK1,X2_42,X0_42,X1_42))
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_42,u1_struct_0(sK1))
    | k13_lattice3(sK1,X2_42,X0_42) = X1_42 ),
    inference(subtyping,[status(esa)],[c_542])).

cnf(c_1300,plain,
    ( ~ r1_orders_2(sK1,sK2,sK0(sK1,sK2,sK3,sK2))
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ r1_orders_2(sK1,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | k13_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1301,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK2,sK0(sK1,sK2,sK3,sK2)) != iProver_top
    | r1_orders_2(sK1,sK2,sK2) != iProver_top
    | r1_orders_2(sK1,sK3,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_7,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k13_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_474,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k13_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_475,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k13_lattice3(sK1,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_479,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k13_lattice3(sK1,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_18,c_16])).

cnf(c_480,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k13_lattice3(sK1,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_479])).

cnf(c_765,plain,
    ( ~ r1_orders_2(sK1,X0_42,X1_42)
    | ~ r1_orders_2(sK1,X2_42,X1_42)
    | r1_orders_2(sK1,X2_42,sK0(sK1,X2_42,X0_42,X1_42))
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_42,u1_struct_0(sK1))
    | k13_lattice3(sK1,X2_42,X0_42) = X1_42 ),
    inference(subtyping,[status(esa)],[c_480])).

cnf(c_1310,plain,
    ( r1_orders_2(sK1,sK2,sK0(sK1,sK2,sK3,sK2))
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ r1_orders_2(sK1,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | k13_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_1311,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK2,sK0(sK1,sK2,sK3,sK2)) = iProver_top
    | r1_orders_2(sK1,sK2,sK2) != iProver_top
    | r1_orders_2(sK1,sK3,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_1324,plain,
    ( r1_orders_2(sK1,sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1134,c_24,c_25,c_789,c_793,c_796,c_799,c_1301,c_1311])).

cnf(c_13,negated_conjecture,
    ( r1_orders_2(sK1,sK3,sK2)
    | k13_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_773,negated_conjecture,
    ( r1_orders_2(sK1,sK3,sK2)
    | k13_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_790,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_788,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_26,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1526,c_1451,c_1399,c_1395,c_1357,c_1324,c_790,c_788,c_12,c_26,c_14,c_15])).


%------------------------------------------------------------------------------
