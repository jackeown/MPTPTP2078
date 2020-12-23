%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1547+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:51 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 968 expanded)
%              Number of clauses        :   95 ( 211 expanded)
%              Number of leaves         :   13 ( 263 expanded)
%              Depth                    :   19
%              Number of atoms          :  774 (7726 expanded)
%              Number of equality atoms :  136 (1442 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
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
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k12_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK0(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k12_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK0(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
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

fof(f51,plain,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_856,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1542,plain,
    ( k12_lattice3(sK1,X0_43,sK3) != X1_43
    | sK2 != X1_43
    | sK2 = k12_lattice3(sK1,X0_43,sK3) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_1543,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK2
    | sK2 = k12_lattice3(sK1,sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_17,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(k12_lattice3(sK1,X0,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(k12_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_18,c_16])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(k12_lattice3(sK1,X1,X0),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_10,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_448,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_449,plain,
    ( r1_orders_2(sK1,k12_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k12_lattice3(sK1,X0,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_451,plain,
    ( r1_orders_2(sK1,k12_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k12_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_18,c_16])).

cnf(c_452,plain,
    ( r1_orders_2(sK1,k12_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k12_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_649,plain,
    ( r1_orders_2(sK1,k12_lattice3(sK1,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_635,c_452])).

cnf(c_839,plain,
    ( r1_orders_2(sK1,k12_lattice3(sK1,X0_43,X1_43),X1_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_649])).

cnf(c_1496,plain,
    ( r1_orders_2(sK1,k12_lattice3(sK1,X0_43,sK3),sK3)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1502,plain,
    ( r1_orders_2(sK1,k12_lattice3(sK1,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_859,plain,
    ( ~ r1_orders_2(X0_42,X0_43,X1_43)
    | r1_orders_2(X0_42,X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_1442,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | r1_orders_2(sK1,sK2,sK3)
    | sK3 != X1_43
    | sK2 != X0_43 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1473,plain,
    ( ~ r1_orders_2(sK1,X0_43,sK3)
    | r1_orders_2(sK1,sK2,sK3)
    | sK3 != sK3
    | sK2 != X0_43 ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_1495,plain,
    ( ~ r1_orders_2(sK1,k12_lattice3(sK1,X0_43,sK3),sK3)
    | r1_orders_2(sK1,sK2,sK3)
    | sK3 != sK3
    | sK2 != k12_lattice3(sK1,X0_43,sK3) ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_1498,plain,
    ( ~ r1_orders_2(sK1,k12_lattice3(sK1,sK2,sK3),sK3)
    | r1_orders_2(sK1,sK2,sK3)
    | sK3 != sK3
    | sK2 != k12_lattice3(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_855,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1474,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_7,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k12_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_534,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK0(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X3,X2) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_535,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k12_lattice3(sK1,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k12_lattice3(sK1,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_18,c_16])).

cnf(c_540,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_843,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | r1_orders_2(sK1,sK0(sK1,X2_43,X1_43,X0_43),X2_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k12_lattice3(sK1,X2_43,X1_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_540])).

cnf(c_1404,plain,
    ( r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
    | ~ r1_orders_2(sK1,sK2,sK3)
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1414,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2) = iProver_top
    | r1_orders_2(sK1,sK2,sK3) != iProver_top
    | r1_orders_2(sK1,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k12_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_596,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK0(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X3,X2) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_597,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k12_lattice3(sK1,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_601,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | k12_lattice3(sK1,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_18,c_16])).

cnf(c_602,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X0,X2)
    | ~ r1_orders_2(sK1,sK0(sK1,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_601])).

cnf(c_841,plain,
    ( ~ r1_orders_2(sK1,X0_43,X1_43)
    | ~ r1_orders_2(sK1,X0_43,X2_43)
    | ~ r1_orders_2(sK1,sK0(sK1,X2_43,X1_43,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK1))
    | k12_lattice3(sK1,X2_43,X1_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_602])).

cnf(c_1406,plain,
    ( ~ r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2)
    | ~ r1_orders_2(sK1,sK2,sK3)
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1410,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK0(sK1,sK2,sK3,sK2),sK2) != iProver_top
    | r1_orders_2(sK1,sK2,sK3) != iProver_top
    | r1_orders_2(sK1,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

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
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_58,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
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

cnf(c_395,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X0 != X3
    | X1 != X3
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_267,c_288])).

cnf(c_396,plain,
    ( r1_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_845,plain,
    ( r1_orders_2(sK1,X0_43,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_845])).

cnf(c_873,plain,
    ( m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_875,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_851,plain,
    ( r1_orders_2(sK1,X0_43,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_845])).

cnf(c_870,plain,
    ( r1_orders_2(sK1,X0_43,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_872,plain,
    ( r1_orders_2(sK1,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_852,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_845])).

cnf(c_869,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_12,negated_conjecture,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_142,plain,
    ( ~ r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_306,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_307,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_311,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_17,c_16,c_58])).

cnf(c_312,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_381,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) != sK2
    | sK3 != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_142,c_312])).

cnf(c_382,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_384,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_15,c_14])).

cnf(c_755,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(prop_impl,[status(thm)],[c_15,c_14,c_382])).

cnf(c_846,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_755])).

cnf(c_868,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK2
    | r1_orders_2(sK1,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_13,negated_conjecture,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_144,plain,
    ( r3_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_367,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK2
    | sK3 != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_144,c_288])).

cnf(c_368,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_370,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_15,c_14])).

cnf(c_757,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(prop_impl,[status(thm)],[c_15,c_14,c_368])).

cnf(c_847,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_757])).

cnf(c_867,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_864,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_372,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK2
    | r1_orders_2(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1543,c_1502,c_1498,c_1474,c_1414,c_1410,c_875,c_872,c_869,c_868,c_867,c_864,c_384,c_372,c_25,c_14,c_24,c_15])).


%------------------------------------------------------------------------------
