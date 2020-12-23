%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:10 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 506 expanded)
%              Number of clauses        :   79 ( 176 expanded)
%              Number of leaves         :   14 ( 122 expanded)
%              Depth                    :   21
%              Number of atoms          :  610 (2177 expanded)
%              Number of equality atoms :   77 ( 148 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f54,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f53,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),sK2,X2),k3_xboole_0(sK2,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
        & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) )
      & v2_lattice3(k2_yellow_1(sK1))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v2_lattice3(k2_yellow_1(sK1))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f39,f38,f37])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_339,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_340,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_12,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_344,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_12])).

cnf(c_345,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_344])).

cnf(c_1056,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0_50),X0_47,X1_47)
    | r3_orders_2(k2_yellow_1(X0_50),X0_47,X1_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50)))
    | v2_struct_0(k2_yellow_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_345])).

cnf(c_2844,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X2_47)
    | r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X2_47)
    | ~ m1_subset_1(X2_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_10525,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2844])).

cnf(c_17,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_257,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_258,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_1060,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0_47,X1_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_3900,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X2_47)
    | ~ m1_subset_1(X2_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X2_47) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_7327,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3900])).

cnf(c_6619,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2844])).

cnf(c_5636,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_3900])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_786,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_787,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_1047,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50)))
    | m1_subset_1(k11_lattice3(k2_yellow_1(X0_50),X0_47,X1_47),u1_struct_0(k2_yellow_1(X0_50))) ),
    inference(subtyping,[status(esa)],[c_787])).

cnf(c_5617,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_1412,plain,
    ( m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50))) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(X0_50),X1_47,X0_47),u1_struct_0(k2_yellow_1(X0_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1062,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1397,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1061,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1398,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | k2_yellow_1(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v5_orders_2(k2_yellow_1(sK1))
    | ~ l1_orders_2(k2_yellow_1(sK1))
    | k12_lattice3(k2_yellow_1(sK1),X0,X1) = k11_lattice3(k2_yellow_1(sK1),X0,X1) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_13,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_41,plain,
    ( v5_orders_2(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_44,plain,
    ( l1_orders_2(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | k12_lattice3(k2_yellow_1(sK1),X0,X1) = k11_lattice3(k2_yellow_1(sK1),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_41,c_44])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | k12_lattice3(k2_yellow_1(sK1),X1,X0) = k11_lattice3(k2_yellow_1(sK1),X1,X0) ),
    inference(renaming,[status(thm)],[c_716])).

cnf(c_1048,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | k12_lattice3(k2_yellow_1(sK1),X1_47,X0_47) = k11_lattice3(k2_yellow_1(sK1),X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_717])).

cnf(c_1411,plain,
    ( k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47) = k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47)
    | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1048])).

cnf(c_1644,plain,
    ( k12_lattice3(k2_yellow_1(sK1),sK2,X0_47) = k11_lattice3(k2_yellow_1(sK1),sK2,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1411])).

cnf(c_1863,plain,
    ( k12_lattice3(k2_yellow_1(sK1),sK2,sK3) = k11_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1397,c_1644])).

cnf(c_11,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_506,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_507,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1)))
    | ~ v5_orders_2(k2_yellow_1(sK1))
    | ~ l1_orders_2(k2_yellow_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_511,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_41,c_44])).

cnf(c_512,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(renaming,[status(thm)],[c_511])).

cnf(c_1055,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_512])).

cnf(c_1404,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1055])).

cnf(c_2907,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) = iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1863,c_1404])).

cnf(c_2912,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) = iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2907,c_1863])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5540,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) = iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2912,c_25,c_26])).

cnf(c_5546,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_5540])).

cnf(c_5547,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5546])).

cnf(c_10,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_530,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_531,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1)))
    | ~ v5_orders_2(k2_yellow_1(sK1))
    | ~ l1_orders_2(k2_yellow_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_533,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_41,c_44])).

cnf(c_534,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(renaming,[status(thm)],[c_533])).

cnf(c_1054,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X1_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_534])).

cnf(c_1405,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X1_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_2952,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1863,c_1405])).

cnf(c_2957,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2952,c_1863])).

cnf(c_2971,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2957])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1064,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | ~ r1_tarski(X0_47,X2_47)
    | r1_tarski(X0_47,k3_xboole_0(X2_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1395,plain,
    ( r1_tarski(X0_47,X1_47) != iProver_top
    | r1_tarski(X0_47,X2_47) != iProver_top
    | r1_tarski(X0_47,k3_xboole_0(X2_47,X1_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1063,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1396,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_1858,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1395,c_1396])).

cnf(c_1859,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1858])).

cnf(c_15,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_35,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10525,c_7327,c_6619,c_5636,c_5617,c_5547,c_2971,c_1859,c_35,c_19,c_20,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.74/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.02  
% 3.74/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/1.02  
% 3.74/1.02  ------  iProver source info
% 3.74/1.02  
% 3.74/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.74/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/1.02  git: non_committed_changes: false
% 3.74/1.02  git: last_make_outside_of_git: false
% 3.74/1.02  
% 3.74/1.02  ------ 
% 3.74/1.02  
% 3.74/1.02  ------ Input Options
% 3.74/1.02  
% 3.74/1.02  --out_options                           all
% 3.74/1.02  --tptp_safe_out                         true
% 3.74/1.02  --problem_path                          ""
% 3.74/1.02  --include_path                          ""
% 3.74/1.02  --clausifier                            res/vclausify_rel
% 3.74/1.02  --clausifier_options                    --mode clausify
% 3.74/1.02  --stdin                                 false
% 3.74/1.02  --stats_out                             all
% 3.74/1.02  
% 3.74/1.02  ------ General Options
% 3.74/1.02  
% 3.74/1.02  --fof                                   false
% 3.74/1.02  --time_out_real                         305.
% 3.74/1.02  --time_out_virtual                      -1.
% 3.74/1.02  --symbol_type_check                     false
% 3.74/1.02  --clausify_out                          false
% 3.74/1.02  --sig_cnt_out                           false
% 3.74/1.02  --trig_cnt_out                          false
% 3.74/1.02  --trig_cnt_out_tolerance                1.
% 3.74/1.02  --trig_cnt_out_sk_spl                   false
% 3.74/1.02  --abstr_cl_out                          false
% 3.74/1.02  
% 3.74/1.02  ------ Global Options
% 3.74/1.02  
% 3.74/1.02  --schedule                              default
% 3.74/1.02  --add_important_lit                     false
% 3.74/1.02  --prop_solver_per_cl                    1000
% 3.74/1.02  --min_unsat_core                        false
% 3.74/1.02  --soft_assumptions                      false
% 3.74/1.02  --soft_lemma_size                       3
% 3.74/1.02  --prop_impl_unit_size                   0
% 3.74/1.02  --prop_impl_unit                        []
% 3.74/1.02  --share_sel_clauses                     true
% 3.74/1.02  --reset_solvers                         false
% 3.74/1.02  --bc_imp_inh                            [conj_cone]
% 3.74/1.02  --conj_cone_tolerance                   3.
% 3.74/1.02  --extra_neg_conj                        none
% 3.74/1.02  --large_theory_mode                     true
% 3.74/1.02  --prolific_symb_bound                   200
% 3.74/1.02  --lt_threshold                          2000
% 3.74/1.02  --clause_weak_htbl                      true
% 3.74/1.02  --gc_record_bc_elim                     false
% 3.74/1.02  
% 3.74/1.02  ------ Preprocessing Options
% 3.74/1.02  
% 3.74/1.02  --preprocessing_flag                    true
% 3.74/1.02  --time_out_prep_mult                    0.1
% 3.74/1.02  --splitting_mode                        input
% 3.74/1.02  --splitting_grd                         true
% 3.74/1.02  --splitting_cvd                         false
% 3.74/1.02  --splitting_cvd_svl                     false
% 3.74/1.02  --splitting_nvd                         32
% 3.74/1.02  --sub_typing                            true
% 3.74/1.02  --prep_gs_sim                           true
% 3.74/1.02  --prep_unflatten                        true
% 3.74/1.02  --prep_res_sim                          true
% 3.74/1.02  --prep_upred                            true
% 3.74/1.02  --prep_sem_filter                       exhaustive
% 3.74/1.02  --prep_sem_filter_out                   false
% 3.74/1.02  --pred_elim                             true
% 3.74/1.02  --res_sim_input                         true
% 3.74/1.02  --eq_ax_congr_red                       true
% 3.74/1.02  --pure_diseq_elim                       true
% 3.74/1.02  --brand_transform                       false
% 3.74/1.02  --non_eq_to_eq                          false
% 3.74/1.02  --prep_def_merge                        true
% 3.74/1.02  --prep_def_merge_prop_impl              false
% 3.74/1.02  --prep_def_merge_mbd                    true
% 3.74/1.02  --prep_def_merge_tr_red                 false
% 3.74/1.02  --prep_def_merge_tr_cl                  false
% 3.74/1.02  --smt_preprocessing                     true
% 3.74/1.02  --smt_ac_axioms                         fast
% 3.74/1.02  --preprocessed_out                      false
% 3.74/1.02  --preprocessed_stats                    false
% 3.74/1.02  
% 3.74/1.02  ------ Abstraction refinement Options
% 3.74/1.02  
% 3.74/1.02  --abstr_ref                             []
% 3.74/1.02  --abstr_ref_prep                        false
% 3.74/1.02  --abstr_ref_until_sat                   false
% 3.74/1.02  --abstr_ref_sig_restrict                funpre
% 3.74/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/1.02  --abstr_ref_under                       []
% 3.74/1.02  
% 3.74/1.02  ------ SAT Options
% 3.74/1.02  
% 3.74/1.02  --sat_mode                              false
% 3.74/1.02  --sat_fm_restart_options                ""
% 3.74/1.02  --sat_gr_def                            false
% 3.74/1.02  --sat_epr_types                         true
% 3.74/1.02  --sat_non_cyclic_types                  false
% 3.74/1.02  --sat_finite_models                     false
% 3.74/1.02  --sat_fm_lemmas                         false
% 3.74/1.02  --sat_fm_prep                           false
% 3.74/1.02  --sat_fm_uc_incr                        true
% 3.74/1.02  --sat_out_model                         small
% 3.74/1.02  --sat_out_clauses                       false
% 3.74/1.02  
% 3.74/1.02  ------ QBF Options
% 3.74/1.02  
% 3.74/1.02  --qbf_mode                              false
% 3.74/1.02  --qbf_elim_univ                         false
% 3.74/1.02  --qbf_dom_inst                          none
% 3.74/1.02  --qbf_dom_pre_inst                      false
% 3.74/1.02  --qbf_sk_in                             false
% 3.74/1.02  --qbf_pred_elim                         true
% 3.74/1.02  --qbf_split                             512
% 3.74/1.02  
% 3.74/1.02  ------ BMC1 Options
% 3.74/1.02  
% 3.74/1.02  --bmc1_incremental                      false
% 3.74/1.02  --bmc1_axioms                           reachable_all
% 3.74/1.02  --bmc1_min_bound                        0
% 3.74/1.02  --bmc1_max_bound                        -1
% 3.74/1.02  --bmc1_max_bound_default                -1
% 3.74/1.02  --bmc1_symbol_reachability              true
% 3.74/1.02  --bmc1_property_lemmas                  false
% 3.74/1.02  --bmc1_k_induction                      false
% 3.74/1.02  --bmc1_non_equiv_states                 false
% 3.74/1.02  --bmc1_deadlock                         false
% 3.74/1.02  --bmc1_ucm                              false
% 3.74/1.02  --bmc1_add_unsat_core                   none
% 3.74/1.02  --bmc1_unsat_core_children              false
% 3.74/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/1.02  --bmc1_out_stat                         full
% 3.74/1.02  --bmc1_ground_init                      false
% 3.74/1.02  --bmc1_pre_inst_next_state              false
% 3.74/1.02  --bmc1_pre_inst_state                   false
% 3.74/1.02  --bmc1_pre_inst_reach_state             false
% 3.74/1.02  --bmc1_out_unsat_core                   false
% 3.74/1.02  --bmc1_aig_witness_out                  false
% 3.74/1.02  --bmc1_verbose                          false
% 3.74/1.02  --bmc1_dump_clauses_tptp                false
% 3.74/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.74/1.02  --bmc1_dump_file                        -
% 3.74/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.74/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.74/1.02  --bmc1_ucm_extend_mode                  1
% 3.74/1.02  --bmc1_ucm_init_mode                    2
% 3.74/1.02  --bmc1_ucm_cone_mode                    none
% 3.74/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.74/1.02  --bmc1_ucm_relax_model                  4
% 3.74/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.74/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/1.02  --bmc1_ucm_layered_model                none
% 3.74/1.02  --bmc1_ucm_max_lemma_size               10
% 3.74/1.02  
% 3.74/1.02  ------ AIG Options
% 3.74/1.02  
% 3.74/1.02  --aig_mode                              false
% 3.74/1.02  
% 3.74/1.02  ------ Instantiation Options
% 3.74/1.02  
% 3.74/1.02  --instantiation_flag                    true
% 3.74/1.02  --inst_sos_flag                         false
% 3.74/1.02  --inst_sos_phase                        true
% 3.74/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/1.02  --inst_lit_sel_side                     num_symb
% 3.74/1.02  --inst_solver_per_active                1400
% 3.74/1.02  --inst_solver_calls_frac                1.
% 3.74/1.02  --inst_passive_queue_type               priority_queues
% 3.74/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/1.02  --inst_passive_queues_freq              [25;2]
% 3.74/1.02  --inst_dismatching                      true
% 3.74/1.02  --inst_eager_unprocessed_to_passive     true
% 3.74/1.02  --inst_prop_sim_given                   true
% 3.74/1.02  --inst_prop_sim_new                     false
% 3.74/1.02  --inst_subs_new                         false
% 3.74/1.02  --inst_eq_res_simp                      false
% 3.74/1.02  --inst_subs_given                       false
% 3.74/1.02  --inst_orphan_elimination               true
% 3.74/1.02  --inst_learning_loop_flag               true
% 3.74/1.02  --inst_learning_start                   3000
% 3.74/1.02  --inst_learning_factor                  2
% 3.74/1.02  --inst_start_prop_sim_after_learn       3
% 3.74/1.02  --inst_sel_renew                        solver
% 3.74/1.02  --inst_lit_activity_flag                true
% 3.74/1.02  --inst_restr_to_given                   false
% 3.74/1.02  --inst_activity_threshold               500
% 3.74/1.02  --inst_out_proof                        true
% 3.74/1.02  
% 3.74/1.02  ------ Resolution Options
% 3.74/1.02  
% 3.74/1.02  --resolution_flag                       true
% 3.74/1.02  --res_lit_sel                           adaptive
% 3.74/1.02  --res_lit_sel_side                      none
% 3.74/1.02  --res_ordering                          kbo
% 3.74/1.02  --res_to_prop_solver                    active
% 3.74/1.02  --res_prop_simpl_new                    false
% 3.74/1.02  --res_prop_simpl_given                  true
% 3.74/1.02  --res_passive_queue_type                priority_queues
% 3.74/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/1.02  --res_passive_queues_freq               [15;5]
% 3.74/1.02  --res_forward_subs                      full
% 3.74/1.02  --res_backward_subs                     full
% 3.74/1.02  --res_forward_subs_resolution           true
% 3.74/1.02  --res_backward_subs_resolution          true
% 3.74/1.02  --res_orphan_elimination                true
% 3.74/1.02  --res_time_limit                        2.
% 3.74/1.02  --res_out_proof                         true
% 3.74/1.02  
% 3.74/1.02  ------ Superposition Options
% 3.74/1.02  
% 3.74/1.02  --superposition_flag                    true
% 3.74/1.02  --sup_passive_queue_type                priority_queues
% 3.74/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.74/1.02  --demod_completeness_check              fast
% 3.74/1.02  --demod_use_ground                      true
% 3.74/1.02  --sup_to_prop_solver                    passive
% 3.74/1.02  --sup_prop_simpl_new                    true
% 3.74/1.02  --sup_prop_simpl_given                  true
% 3.74/1.02  --sup_fun_splitting                     false
% 3.74/1.02  --sup_smt_interval                      50000
% 3.74/1.02  
% 3.74/1.02  ------ Superposition Simplification Setup
% 3.74/1.02  
% 3.74/1.02  --sup_indices_passive                   []
% 3.74/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.02  --sup_full_bw                           [BwDemod]
% 3.74/1.02  --sup_immed_triv                        [TrivRules]
% 3.74/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.02  --sup_immed_bw_main                     []
% 3.74/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/1.02  
% 3.74/1.02  ------ Combination Options
% 3.74/1.02  
% 3.74/1.02  --comb_res_mult                         3
% 3.74/1.02  --comb_sup_mult                         2
% 3.74/1.02  --comb_inst_mult                        10
% 3.74/1.02  
% 3.74/1.02  ------ Debug Options
% 3.74/1.02  
% 3.74/1.02  --dbg_backtrace                         false
% 3.74/1.02  --dbg_dump_prop_clauses                 false
% 3.74/1.02  --dbg_dump_prop_clauses_file            -
% 3.74/1.02  --dbg_out_stat                          false
% 3.74/1.02  ------ Parsing...
% 3.74/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/1.02  
% 3.74/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.74/1.02  
% 3.74/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/1.02  
% 3.74/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.02  ------ Proving...
% 3.74/1.02  ------ Problem Properties 
% 3.74/1.02  
% 3.74/1.02  
% 3.74/1.02  clauses                                 18
% 3.74/1.02  conjectures                             3
% 3.74/1.02  EPR                                     0
% 3.74/1.02  Horn                                    13
% 3.74/1.02  unary                                   4
% 3.74/1.02  binary                                  0
% 3.74/1.02  lits                                    74
% 3.74/1.02  lits eq                                 5
% 3.74/1.02  fd_pure                                 0
% 3.74/1.02  fd_pseudo                               0
% 3.74/1.02  fd_cond                                 0
% 3.74/1.02  fd_pseudo_cond                          4
% 3.74/1.02  AC symbols                              0
% 3.74/1.02  
% 3.74/1.02  ------ Schedule dynamic 5 is on 
% 3.74/1.02  
% 3.74/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.74/1.02  
% 3.74/1.02  
% 3.74/1.02  ------ 
% 3.74/1.02  Current options:
% 3.74/1.02  ------ 
% 3.74/1.02  
% 3.74/1.02  ------ Input Options
% 3.74/1.02  
% 3.74/1.02  --out_options                           all
% 3.74/1.02  --tptp_safe_out                         true
% 3.74/1.02  --problem_path                          ""
% 3.74/1.02  --include_path                          ""
% 3.74/1.02  --clausifier                            res/vclausify_rel
% 3.74/1.02  --clausifier_options                    --mode clausify
% 3.74/1.02  --stdin                                 false
% 3.74/1.02  --stats_out                             all
% 3.74/1.02  
% 3.74/1.02  ------ General Options
% 3.74/1.02  
% 3.74/1.02  --fof                                   false
% 3.74/1.02  --time_out_real                         305.
% 3.74/1.02  --time_out_virtual                      -1.
% 3.74/1.02  --symbol_type_check                     false
% 3.74/1.02  --clausify_out                          false
% 3.74/1.02  --sig_cnt_out                           false
% 3.74/1.02  --trig_cnt_out                          false
% 3.74/1.02  --trig_cnt_out_tolerance                1.
% 3.74/1.02  --trig_cnt_out_sk_spl                   false
% 3.74/1.02  --abstr_cl_out                          false
% 3.74/1.02  
% 3.74/1.02  ------ Global Options
% 3.74/1.02  
% 3.74/1.02  --schedule                              default
% 3.74/1.02  --add_important_lit                     false
% 3.74/1.02  --prop_solver_per_cl                    1000
% 3.74/1.02  --min_unsat_core                        false
% 3.74/1.02  --soft_assumptions                      false
% 3.74/1.02  --soft_lemma_size                       3
% 3.74/1.02  --prop_impl_unit_size                   0
% 3.74/1.02  --prop_impl_unit                        []
% 3.74/1.02  --share_sel_clauses                     true
% 3.74/1.02  --reset_solvers                         false
% 3.74/1.02  --bc_imp_inh                            [conj_cone]
% 3.74/1.02  --conj_cone_tolerance                   3.
% 3.74/1.02  --extra_neg_conj                        none
% 3.74/1.02  --large_theory_mode                     true
% 3.74/1.02  --prolific_symb_bound                   200
% 3.74/1.02  --lt_threshold                          2000
% 3.74/1.02  --clause_weak_htbl                      true
% 3.74/1.02  --gc_record_bc_elim                     false
% 3.74/1.02  
% 3.74/1.02  ------ Preprocessing Options
% 3.74/1.02  
% 3.74/1.02  --preprocessing_flag                    true
% 3.74/1.02  --time_out_prep_mult                    0.1
% 3.74/1.02  --splitting_mode                        input
% 3.74/1.02  --splitting_grd                         true
% 3.74/1.02  --splitting_cvd                         false
% 3.74/1.02  --splitting_cvd_svl                     false
% 3.74/1.02  --splitting_nvd                         32
% 3.74/1.02  --sub_typing                            true
% 3.74/1.02  --prep_gs_sim                           true
% 3.74/1.02  --prep_unflatten                        true
% 3.74/1.02  --prep_res_sim                          true
% 3.74/1.02  --prep_upred                            true
% 3.74/1.02  --prep_sem_filter                       exhaustive
% 3.74/1.02  --prep_sem_filter_out                   false
% 3.74/1.02  --pred_elim                             true
% 3.74/1.02  --res_sim_input                         true
% 3.74/1.02  --eq_ax_congr_red                       true
% 3.74/1.02  --pure_diseq_elim                       true
% 3.74/1.02  --brand_transform                       false
% 3.74/1.02  --non_eq_to_eq                          false
% 3.74/1.02  --prep_def_merge                        true
% 3.74/1.02  --prep_def_merge_prop_impl              false
% 3.74/1.02  --prep_def_merge_mbd                    true
% 3.74/1.02  --prep_def_merge_tr_red                 false
% 3.74/1.02  --prep_def_merge_tr_cl                  false
% 3.74/1.02  --smt_preprocessing                     true
% 3.74/1.02  --smt_ac_axioms                         fast
% 3.74/1.02  --preprocessed_out                      false
% 3.74/1.02  --preprocessed_stats                    false
% 3.74/1.02  
% 3.74/1.02  ------ Abstraction refinement Options
% 3.74/1.02  
% 3.74/1.02  --abstr_ref                             []
% 3.74/1.02  --abstr_ref_prep                        false
% 3.74/1.02  --abstr_ref_until_sat                   false
% 3.74/1.02  --abstr_ref_sig_restrict                funpre
% 3.74/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/1.02  --abstr_ref_under                       []
% 3.74/1.02  
% 3.74/1.02  ------ SAT Options
% 3.74/1.02  
% 3.74/1.02  --sat_mode                              false
% 3.74/1.02  --sat_fm_restart_options                ""
% 3.74/1.02  --sat_gr_def                            false
% 3.74/1.02  --sat_epr_types                         true
% 3.74/1.02  --sat_non_cyclic_types                  false
% 3.74/1.02  --sat_finite_models                     false
% 3.74/1.02  --sat_fm_lemmas                         false
% 3.74/1.02  --sat_fm_prep                           false
% 3.74/1.02  --sat_fm_uc_incr                        true
% 3.74/1.02  --sat_out_model                         small
% 3.74/1.02  --sat_out_clauses                       false
% 3.74/1.02  
% 3.74/1.02  ------ QBF Options
% 3.74/1.02  
% 3.74/1.02  --qbf_mode                              false
% 3.74/1.02  --qbf_elim_univ                         false
% 3.74/1.02  --qbf_dom_inst                          none
% 3.74/1.02  --qbf_dom_pre_inst                      false
% 3.74/1.02  --qbf_sk_in                             false
% 3.74/1.02  --qbf_pred_elim                         true
% 3.74/1.02  --qbf_split                             512
% 3.74/1.02  
% 3.74/1.02  ------ BMC1 Options
% 3.74/1.02  
% 3.74/1.02  --bmc1_incremental                      false
% 3.74/1.02  --bmc1_axioms                           reachable_all
% 3.74/1.02  --bmc1_min_bound                        0
% 3.74/1.02  --bmc1_max_bound                        -1
% 3.74/1.02  --bmc1_max_bound_default                -1
% 3.74/1.02  --bmc1_symbol_reachability              true
% 3.74/1.02  --bmc1_property_lemmas                  false
% 3.74/1.02  --bmc1_k_induction                      false
% 3.74/1.02  --bmc1_non_equiv_states                 false
% 3.74/1.02  --bmc1_deadlock                         false
% 3.74/1.02  --bmc1_ucm                              false
% 3.74/1.02  --bmc1_add_unsat_core                   none
% 3.74/1.02  --bmc1_unsat_core_children              false
% 3.74/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/1.02  --bmc1_out_stat                         full
% 3.74/1.02  --bmc1_ground_init                      false
% 3.74/1.02  --bmc1_pre_inst_next_state              false
% 3.74/1.02  --bmc1_pre_inst_state                   false
% 3.74/1.02  --bmc1_pre_inst_reach_state             false
% 3.74/1.02  --bmc1_out_unsat_core                   false
% 3.74/1.02  --bmc1_aig_witness_out                  false
% 3.74/1.02  --bmc1_verbose                          false
% 3.74/1.02  --bmc1_dump_clauses_tptp                false
% 3.74/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.74/1.02  --bmc1_dump_file                        -
% 3.74/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.74/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.74/1.02  --bmc1_ucm_extend_mode                  1
% 3.74/1.02  --bmc1_ucm_init_mode                    2
% 3.74/1.02  --bmc1_ucm_cone_mode                    none
% 3.74/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.74/1.02  --bmc1_ucm_relax_model                  4
% 3.74/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.74/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/1.02  --bmc1_ucm_layered_model                none
% 3.74/1.02  --bmc1_ucm_max_lemma_size               10
% 3.74/1.02  
% 3.74/1.02  ------ AIG Options
% 3.74/1.02  
% 3.74/1.02  --aig_mode                              false
% 3.74/1.02  
% 3.74/1.02  ------ Instantiation Options
% 3.74/1.02  
% 3.74/1.02  --instantiation_flag                    true
% 3.74/1.02  --inst_sos_flag                         false
% 3.74/1.02  --inst_sos_phase                        true
% 3.74/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/1.02  --inst_lit_sel_side                     none
% 3.74/1.02  --inst_solver_per_active                1400
% 3.74/1.02  --inst_solver_calls_frac                1.
% 3.74/1.02  --inst_passive_queue_type               priority_queues
% 3.74/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/1.02  --inst_passive_queues_freq              [25;2]
% 3.74/1.02  --inst_dismatching                      true
% 3.74/1.02  --inst_eager_unprocessed_to_passive     true
% 3.74/1.02  --inst_prop_sim_given                   true
% 3.74/1.02  --inst_prop_sim_new                     false
% 3.74/1.02  --inst_subs_new                         false
% 3.74/1.02  --inst_eq_res_simp                      false
% 3.74/1.02  --inst_subs_given                       false
% 3.74/1.02  --inst_orphan_elimination               true
% 3.74/1.02  --inst_learning_loop_flag               true
% 3.74/1.02  --inst_learning_start                   3000
% 3.74/1.02  --inst_learning_factor                  2
% 3.74/1.02  --inst_start_prop_sim_after_learn       3
% 3.74/1.02  --inst_sel_renew                        solver
% 3.74/1.02  --inst_lit_activity_flag                true
% 3.74/1.02  --inst_restr_to_given                   false
% 3.74/1.02  --inst_activity_threshold               500
% 3.74/1.02  --inst_out_proof                        true
% 3.74/1.02  
% 3.74/1.02  ------ Resolution Options
% 3.74/1.02  
% 3.74/1.02  --resolution_flag                       false
% 3.74/1.02  --res_lit_sel                           adaptive
% 3.74/1.02  --res_lit_sel_side                      none
% 3.74/1.02  --res_ordering                          kbo
% 3.74/1.02  --res_to_prop_solver                    active
% 3.74/1.02  --res_prop_simpl_new                    false
% 3.74/1.02  --res_prop_simpl_given                  true
% 3.74/1.02  --res_passive_queue_type                priority_queues
% 3.74/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/1.02  --res_passive_queues_freq               [15;5]
% 3.74/1.02  --res_forward_subs                      full
% 3.74/1.02  --res_backward_subs                     full
% 3.74/1.02  --res_forward_subs_resolution           true
% 3.74/1.02  --res_backward_subs_resolution          true
% 3.74/1.02  --res_orphan_elimination                true
% 3.74/1.02  --res_time_limit                        2.
% 3.74/1.02  --res_out_proof                         true
% 3.74/1.02  
% 3.74/1.02  ------ Superposition Options
% 3.74/1.02  
% 3.74/1.02  --superposition_flag                    true
% 3.74/1.02  --sup_passive_queue_type                priority_queues
% 3.74/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.74/1.02  --demod_completeness_check              fast
% 3.74/1.02  --demod_use_ground                      true
% 3.74/1.02  --sup_to_prop_solver                    passive
% 3.74/1.02  --sup_prop_simpl_new                    true
% 3.74/1.02  --sup_prop_simpl_given                  true
% 3.74/1.02  --sup_fun_splitting                     false
% 3.74/1.02  --sup_smt_interval                      50000
% 3.74/1.02  
% 3.74/1.02  ------ Superposition Simplification Setup
% 3.74/1.02  
% 3.74/1.02  --sup_indices_passive                   []
% 3.74/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.02  --sup_full_bw                           [BwDemod]
% 3.74/1.02  --sup_immed_triv                        [TrivRules]
% 3.74/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.02  --sup_immed_bw_main                     []
% 3.74/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/1.02  
% 3.74/1.02  ------ Combination Options
% 3.74/1.02  
% 3.74/1.02  --comb_res_mult                         3
% 3.74/1.02  --comb_sup_mult                         2
% 3.74/1.02  --comb_inst_mult                        10
% 3.74/1.02  
% 3.74/1.02  ------ Debug Options
% 3.74/1.02  
% 3.74/1.02  --dbg_backtrace                         false
% 3.74/1.02  --dbg_dump_prop_clauses                 false
% 3.74/1.02  --dbg_dump_prop_clauses_file            -
% 3.74/1.02  --dbg_out_stat                          false
% 3.74/1.02  
% 3.74/1.02  
% 3.74/1.02  
% 3.74/1.02  
% 3.74/1.02  ------ Proving...
% 3.74/1.02  
% 3.74/1.02  
% 3.74/1.02  % SZS status Theorem for theBenchmark.p
% 3.74/1.02  
% 3.74/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/1.02  
% 3.74/1.02  fof(f2,axiom,(
% 3.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f18,plain,(
% 3.74/1.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.74/1.02    inference(ennf_transformation,[],[f2])).
% 3.74/1.02  
% 3.74/1.02  fof(f19,plain,(
% 3.74/1.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.74/1.02    inference(flattening,[],[f18])).
% 3.74/1.02  
% 3.74/1.02  fof(f30,plain,(
% 3.74/1.02    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.74/1.02    inference(nnf_transformation,[],[f19])).
% 3.74/1.02  
% 3.74/1.02  fof(f43,plain,(
% 3.74/1.02    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.74/1.02    inference(cnf_transformation,[],[f30])).
% 3.74/1.02  
% 3.74/1.02  fof(f7,axiom,(
% 3.74/1.02    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f12,plain,(
% 3.74/1.02    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.74/1.02    inference(pure_predicate_removal,[],[f7])).
% 3.74/1.02  
% 3.74/1.02  fof(f14,plain,(
% 3.74/1.02    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 3.74/1.02    inference(pure_predicate_removal,[],[f12])).
% 3.74/1.02  
% 3.74/1.02  fof(f54,plain,(
% 3.74/1.02    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.74/1.02    inference(cnf_transformation,[],[f14])).
% 3.74/1.02  
% 3.74/1.02  fof(f6,axiom,(
% 3.74/1.02    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f13,plain,(
% 3.74/1.02    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.74/1.02    inference(pure_predicate_removal,[],[f6])).
% 3.74/1.02  
% 3.74/1.02  fof(f53,plain,(
% 3.74/1.02    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.74/1.02    inference(cnf_transformation,[],[f13])).
% 3.74/1.02  
% 3.74/1.02  fof(f9,axiom,(
% 3.74/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f27,plain,(
% 3.74/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.74/1.02    inference(ennf_transformation,[],[f9])).
% 3.74/1.02  
% 3.74/1.02  fof(f36,plain,(
% 3.74/1.02    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.74/1.02    inference(nnf_transformation,[],[f27])).
% 3.74/1.02  
% 3.74/1.02  fof(f57,plain,(
% 3.74/1.02    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.74/1.02    inference(cnf_transformation,[],[f36])).
% 3.74/1.02  
% 3.74/1.02  fof(f10,conjecture,(
% 3.74/1.02    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f11,negated_conjecture,(
% 3.74/1.02    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 3.74/1.02    inference(negated_conjecture,[],[f10])).
% 3.74/1.02  
% 3.74/1.02  fof(f28,plain,(
% 3.74/1.02    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 3.74/1.02    inference(ennf_transformation,[],[f11])).
% 3.74/1.02  
% 3.74/1.02  fof(f29,plain,(
% 3.74/1.02    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 3.74/1.02    inference(flattening,[],[f28])).
% 3.74/1.02  
% 3.74/1.02  fof(f39,plain,(
% 3.74/1.02    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.74/1.02    introduced(choice_axiom,[])).
% 3.74/1.02  
% 3.74/1.02  fof(f38,plain,(
% 3.74/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),sK2,X2),k3_xboole_0(sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.74/1.02    introduced(choice_axiom,[])).
% 3.74/1.02  
% 3.74/1.02  fof(f37,plain,(
% 3.74/1.02    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 3.74/1.02    introduced(choice_axiom,[])).
% 3.74/1.02  
% 3.74/1.02  fof(f40,plain,(
% 3.74/1.02    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 3.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f39,f38,f37])).
% 3.74/1.02  
% 3.74/1.02  fof(f59,plain,(
% 3.74/1.02    ~v1_xboole_0(sK1)),
% 3.74/1.02    inference(cnf_transformation,[],[f40])).
% 3.74/1.02  
% 3.74/1.02  fof(f3,axiom,(
% 3.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f20,plain,(
% 3.74/1.02    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 3.74/1.02    inference(ennf_transformation,[],[f3])).
% 3.74/1.02  
% 3.74/1.02  fof(f21,plain,(
% 3.74/1.02    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.74/1.02    inference(flattening,[],[f20])).
% 3.74/1.02  
% 3.74/1.02  fof(f44,plain,(
% 3.74/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.74/1.02    inference(cnf_transformation,[],[f21])).
% 3.74/1.02  
% 3.74/1.02  fof(f62,plain,(
% 3.74/1.02    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 3.74/1.02    inference(cnf_transformation,[],[f40])).
% 3.74/1.02  
% 3.74/1.02  fof(f61,plain,(
% 3.74/1.02    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 3.74/1.02    inference(cnf_transformation,[],[f40])).
% 3.74/1.02  
% 3.74/1.02  fof(f4,axiom,(
% 3.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f22,plain,(
% 3.74/1.02    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.74/1.02    inference(ennf_transformation,[],[f4])).
% 3.74/1.02  
% 3.74/1.02  fof(f23,plain,(
% 3.74/1.02    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.74/1.02    inference(flattening,[],[f22])).
% 3.74/1.02  
% 3.74/1.02  fof(f45,plain,(
% 3.74/1.02    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.74/1.02    inference(cnf_transformation,[],[f23])).
% 3.74/1.02  
% 3.74/1.02  fof(f60,plain,(
% 3.74/1.02    v2_lattice3(k2_yellow_1(sK1))),
% 3.74/1.02    inference(cnf_transformation,[],[f40])).
% 3.74/1.02  
% 3.74/1.02  fof(f55,plain,(
% 3.74/1.02    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.74/1.02    inference(cnf_transformation,[],[f14])).
% 3.74/1.02  
% 3.74/1.02  fof(f5,axiom,(
% 3.74/1.02    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f24,plain,(
% 3.74/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.74/1.02    inference(ennf_transformation,[],[f5])).
% 3.74/1.02  
% 3.74/1.02  fof(f25,plain,(
% 3.74/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.74/1.02    inference(flattening,[],[f24])).
% 3.74/1.02  
% 3.74/1.02  fof(f31,plain,(
% 3.74/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.74/1.02    inference(nnf_transformation,[],[f25])).
% 3.74/1.02  
% 3.74/1.02  fof(f32,plain,(
% 3.74/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.74/1.02    inference(flattening,[],[f31])).
% 3.74/1.02  
% 3.74/1.02  fof(f33,plain,(
% 3.74/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.74/1.02    inference(rectify,[],[f32])).
% 3.74/1.02  
% 3.74/1.02  fof(f34,plain,(
% 3.74/1.02    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.74/1.02    introduced(choice_axiom,[])).
% 3.74/1.02  
% 3.74/1.02  fof(f35,plain,(
% 3.74/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.74/1.02  
% 3.74/1.02  fof(f46,plain,(
% 3.74/1.02    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.74/1.02    inference(cnf_transformation,[],[f35])).
% 3.74/1.02  
% 3.74/1.02  fof(f66,plain,(
% 3.74/1.02    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.74/1.02    inference(equality_resolution,[],[f46])).
% 3.74/1.02  
% 3.74/1.02  fof(f47,plain,(
% 3.74/1.02    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k12_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.74/1.02    inference(cnf_transformation,[],[f35])).
% 3.74/1.02  
% 3.74/1.02  fof(f65,plain,(
% 3.74/1.02    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.74/1.02    inference(equality_resolution,[],[f47])).
% 3.74/1.02  
% 3.74/1.02  fof(f1,axiom,(
% 3.74/1.02    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f16,plain,(
% 3.74/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.74/1.02    inference(ennf_transformation,[],[f1])).
% 3.74/1.02  
% 3.74/1.02  fof(f17,plain,(
% 3.74/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.74/1.02    inference(flattening,[],[f16])).
% 3.74/1.02  
% 3.74/1.02  fof(f41,plain,(
% 3.74/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.74/1.02    inference(cnf_transformation,[],[f17])).
% 3.74/1.02  
% 3.74/1.02  fof(f63,plain,(
% 3.74/1.02    ~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))),
% 3.74/1.02    inference(cnf_transformation,[],[f40])).
% 3.74/1.02  
% 3.74/1.02  fof(f8,axiom,(
% 3.74/1.02    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 3.74/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.02  
% 3.74/1.02  fof(f15,plain,(
% 3.74/1.02    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 3.74/1.02    inference(pure_predicate_removal,[],[f8])).
% 3.74/1.02  
% 3.74/1.02  fof(f26,plain,(
% 3.74/1.02    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 3.74/1.02    inference(ennf_transformation,[],[f15])).
% 3.74/1.02  
% 3.74/1.02  fof(f56,plain,(
% 3.74/1.02    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 3.74/1.02    inference(cnf_transformation,[],[f26])).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1,plain,
% 3.74/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 3.74/1.02      | r3_orders_2(X0,X1,X2)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.02      | v2_struct_0(X0)
% 3.74/1.02      | ~ v3_orders_2(X0)
% 3.74/1.02      | ~ l1_orders_2(X0) ),
% 3.74/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_14,plain,
% 3.74/1.02      ( v3_orders_2(k2_yellow_1(X0)) ),
% 3.74/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_339,plain,
% 3.74/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 3.74/1.02      | r3_orders_2(X0,X1,X2)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.02      | v2_struct_0(X0)
% 3.74/1.02      | ~ l1_orders_2(X0)
% 3.74/1.02      | k2_yellow_1(X3) != X0 ),
% 3.74/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_340,plain,
% 3.74/1.02      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.74/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | v2_struct_0(k2_yellow_1(X0))
% 3.74/1.02      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.74/1.02      inference(unflattening,[status(thm)],[c_339]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_12,plain,
% 3.74/1.02      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.74/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_344,plain,
% 3.74/1.02      ( v2_struct_0(k2_yellow_1(X0))
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.74/1.02      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 3.74/1.02      inference(global_propositional_subsumption,
% 3.74/1.02                [status(thm)],
% 3.74/1.02                [c_340,c_12]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_345,plain,
% 3.74/1.02      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.74/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.74/1.02      inference(renaming,[status(thm)],[c_344]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1056,plain,
% 3.74/1.02      ( ~ r1_orders_2(k2_yellow_1(X0_50),X0_47,X1_47)
% 3.74/1.02      | r3_orders_2(k2_yellow_1(X0_50),X0_47,X1_47)
% 3.74/1.02      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50)))
% 3.74/1.02      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50)))
% 3.74/1.02      | v2_struct_0(k2_yellow_1(X0_50)) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_345]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_2844,plain,
% 3.74/1.02      ( ~ r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X2_47)
% 3.74/1.02      | r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X2_47)
% 3.74/1.02      | ~ m1_subset_1(X2_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | v2_struct_0(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_1056]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_10525,plain,
% 3.74/1.02      ( ~ r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 3.74/1.02      | r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 3.74/1.02      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | v2_struct_0(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_2844]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_17,plain,
% 3.74/1.02      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | r1_tarski(X1,X2)
% 3.74/1.02      | v1_xboole_0(X0) ),
% 3.74/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_22,negated_conjecture,
% 3.74/1.02      ( ~ v1_xboole_0(sK1) ),
% 3.74/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_257,plain,
% 3.74/1.02      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.74/1.02      | r1_tarski(X1,X2)
% 3.74/1.02      | sK1 != X0 ),
% 3.74/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_258,plain,
% 3.74/1.02      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 3.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | r1_tarski(X0,X1) ),
% 3.74/1.02      inference(unflattening,[status(thm)],[c_257]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1060,plain,
% 3.74/1.02      ( ~ r3_orders_2(k2_yellow_1(sK1),X0_47,X1_47)
% 3.74/1.02      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | r1_tarski(X0_47,X1_47) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_258]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_3900,plain,
% 3.74/1.02      ( ~ r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X2_47)
% 3.74/1.02      | ~ m1_subset_1(X2_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X2_47) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_1060]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_7327,plain,
% 3.74/1.02      ( ~ r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 3.74/1.02      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_3900]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_6619,plain,
% 3.74/1.02      ( ~ r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.74/1.02      | r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.74/1.02      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | v2_struct_0(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_2844]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_5636,plain,
% 3.74/1.02      ( ~ r3_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.74/1.02      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_3900]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_3,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.74/1.02      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.74/1.02      | ~ l1_orders_2(X1) ),
% 3.74/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_786,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.74/1.02      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.74/1.02      | k2_yellow_1(X3) != X1 ),
% 3.74/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_787,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.74/1.02      | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
% 3.74/1.02      inference(unflattening,[status(thm)],[c_786]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1047,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50)))
% 3.74/1.02      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50)))
% 3.74/1.02      | m1_subset_1(k11_lattice3(k2_yellow_1(X0_50),X0_47,X1_47),u1_struct_0(k2_yellow_1(X0_50))) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_787]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_5617,plain,
% 3.74/1.02      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_1047]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1412,plain,
% 3.74/1.02      ( m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50))) != iProver_top
% 3.74/1.02      | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50))) != iProver_top
% 3.74/1.02      | m1_subset_1(k11_lattice3(k2_yellow_1(X0_50),X1_47,X0_47),u1_struct_0(k2_yellow_1(X0_50))) = iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_19,negated_conjecture,
% 3.74/1.02      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1062,negated_conjecture,
% 3.74/1.02      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1397,plain,
% 3.74/1.02      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1062]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_20,negated_conjecture,
% 3.74/1.02      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1061,negated_conjecture,
% 3.74/1.02      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_20]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1398,plain,
% 3.74/1.02      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1061]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_4,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.74/1.02      | ~ v5_orders_2(X1)
% 3.74/1.02      | ~ v2_lattice3(X1)
% 3.74/1.02      | ~ l1_orders_2(X1)
% 3.74/1.02      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 3.74/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_21,negated_conjecture,
% 3.74/1.02      ( v2_lattice3(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_711,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.74/1.02      | ~ v5_orders_2(X1)
% 3.74/1.02      | ~ l1_orders_2(X1)
% 3.74/1.02      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 3.74/1.02      | k2_yellow_1(sK1) != X1 ),
% 3.74/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_712,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ v5_orders_2(k2_yellow_1(sK1))
% 3.74/1.02      | ~ l1_orders_2(k2_yellow_1(sK1))
% 3.74/1.02      | k12_lattice3(k2_yellow_1(sK1),X0,X1) = k11_lattice3(k2_yellow_1(sK1),X0,X1) ),
% 3.74/1.02      inference(unflattening,[status(thm)],[c_711]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_13,plain,
% 3.74/1.02      ( v5_orders_2(k2_yellow_1(X0)) ),
% 3.74/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_41,plain,
% 3.74/1.02      ( v5_orders_2(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_44,plain,
% 3.74/1.02      ( l1_orders_2(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_716,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | k12_lattice3(k2_yellow_1(sK1),X0,X1) = k11_lattice3(k2_yellow_1(sK1),X0,X1) ),
% 3.74/1.02      inference(global_propositional_subsumption,
% 3.74/1.02                [status(thm)],
% 3.74/1.02                [c_712,c_41,c_44]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_717,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | k12_lattice3(k2_yellow_1(sK1),X1,X0) = k11_lattice3(k2_yellow_1(sK1),X1,X0) ),
% 3.74/1.02      inference(renaming,[status(thm)],[c_716]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1048,plain,
% 3.74/1.02      ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | k12_lattice3(k2_yellow_1(sK1),X1_47,X0_47) = k11_lattice3(k2_yellow_1(sK1),X1_47,X0_47) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_717]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1411,plain,
% 3.74/1.02      ( k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47) = k11_lattice3(k2_yellow_1(sK1),X0_47,X1_47)
% 3.74/1.02      | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1048]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1644,plain,
% 3.74/1.02      ( k12_lattice3(k2_yellow_1(sK1),sK2,X0_47) = k11_lattice3(k2_yellow_1(sK1),sK2,X0_47)
% 3.74/1.02      | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(superposition,[status(thm)],[c_1398,c_1411]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1863,plain,
% 3.74/1.02      ( k12_lattice3(k2_yellow_1(sK1),sK2,sK3) = k11_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 3.74/1.02      inference(superposition,[status(thm)],[c_1397,c_1644]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_11,plain,
% 3.74/1.02      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.74/1.02      | ~ v5_orders_2(X0)
% 3.74/1.02      | ~ v2_lattice3(X0)
% 3.74/1.02      | ~ l1_orders_2(X0) ),
% 3.74/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_506,plain,
% 3.74/1.02      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.74/1.02      | ~ v5_orders_2(X0)
% 3.74/1.02      | ~ l1_orders_2(X0)
% 3.74/1.02      | k2_yellow_1(sK1) != X0 ),
% 3.74/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_507,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X0)
% 3.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ v5_orders_2(k2_yellow_1(sK1))
% 3.74/1.02      | ~ l1_orders_2(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(unflattening,[status(thm)],[c_506]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_511,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X0)
% 3.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(global_propositional_subsumption,
% 3.74/1.02                [status(thm)],
% 3.74/1.02                [c_507,c_41,c_44]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_512,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X0)
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(renaming,[status(thm)],[c_511]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1055,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X0_47)
% 3.74/1.02      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_512]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1404,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X0_47) = iProver_top
% 3.74/1.02      | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1055]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_2907,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) = iProver_top
% 3.74/1.02      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(superposition,[status(thm)],[c_1863,c_1404]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_2912,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) = iProver_top
% 3.74/1.02      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(light_normalisation,[status(thm)],[c_2907,c_1863]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_25,plain,
% 3.74/1.02      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_26,plain,
% 3.74/1.02      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_5540,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) = iProver_top
% 3.74/1.02      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(global_propositional_subsumption,
% 3.74/1.02                [status(thm)],
% 3.74/1.02                [c_2912,c_25,c_26]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_5546,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) = iProver_top
% 3.74/1.02      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(superposition,[status(thm)],[c_1412,c_5540]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_5547,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 3.74/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_5546]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_10,plain,
% 3.74/1.02      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.74/1.02      | ~ v5_orders_2(X0)
% 3.74/1.02      | ~ v2_lattice3(X0)
% 3.74/1.02      | ~ l1_orders_2(X0) ),
% 3.74/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_530,plain,
% 3.74/1.02      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
% 3.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.74/1.02      | ~ v5_orders_2(X0)
% 3.74/1.02      | ~ l1_orders_2(X0)
% 3.74/1.02      | k2_yellow_1(sK1) != X0 ),
% 3.74/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_531,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X1)
% 3.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ v5_orders_2(k2_yellow_1(sK1))
% 3.74/1.02      | ~ l1_orders_2(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(unflattening,[status(thm)],[c_530]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_533,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X1)
% 3.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(global_propositional_subsumption,
% 3.74/1.02                [status(thm)],
% 3.74/1.02                [c_531,c_41,c_44]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_534,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,X1),X1)
% 3.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(renaming,[status(thm)],[c_533]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1054,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X1_47)
% 3.74/1.02      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_534]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1405,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),X1_47) = iProver_top
% 3.74/1.02      | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(k12_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1054]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_2952,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top
% 3.74/1.02      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(superposition,[status(thm)],[c_1863,c_1405]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_2957,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top
% 3.74/1.02      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.74/1.02      | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 3.74/1.02      inference(light_normalisation,[status(thm)],[c_2952,c_1863]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_2971,plain,
% 3.74/1.02      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.74/1.02      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.74/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.74/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2957]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_0,plain,
% 3.74/1.02      ( ~ r1_tarski(X0,X1)
% 3.74/1.02      | ~ r1_tarski(X0,X2)
% 3.74/1.02      | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 3.74/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1064,plain,
% 3.74/1.02      ( ~ r1_tarski(X0_47,X1_47)
% 3.74/1.02      | ~ r1_tarski(X0_47,X2_47)
% 3.74/1.02      | r1_tarski(X0_47,k3_xboole_0(X2_47,X1_47)) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1395,plain,
% 3.74/1.02      ( r1_tarski(X0_47,X1_47) != iProver_top
% 3.74/1.02      | r1_tarski(X0_47,X2_47) != iProver_top
% 3.74/1.02      | r1_tarski(X0_47,k3_xboole_0(X2_47,X1_47)) = iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1064]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_18,negated_conjecture,
% 3.74/1.02      ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
% 3.74/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1063,negated_conjecture,
% 3.74/1.02      ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
% 3.74/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1396,plain,
% 3.74/1.02      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) != iProver_top ),
% 3.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1858,plain,
% 3.74/1.02      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
% 3.74/1.02      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
% 3.74/1.02      inference(superposition,[status(thm)],[c_1395,c_1396]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_1859,plain,
% 3.74/1.02      ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.74/1.02      | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
% 3.74/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1858]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_15,plain,
% 3.74/1.02      ( v1_xboole_0(X0) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 3.74/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(c_35,plain,
% 3.74/1.02      ( v1_xboole_0(sK1) | ~ v2_struct_0(k2_yellow_1(sK1)) ),
% 3.74/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.74/1.02  
% 3.74/1.02  cnf(contradiction,plain,
% 3.74/1.02      ( $false ),
% 3.74/1.02      inference(minisat,
% 3.74/1.02                [status(thm)],
% 3.74/1.02                [c_10525,c_7327,c_6619,c_5636,c_5617,c_5547,c_2971,
% 3.74/1.02                 c_1859,c_35,c_19,c_20,c_22]) ).
% 3.74/1.02  
% 3.74/1.02  
% 3.74/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/1.02  
% 3.74/1.02  ------                               Statistics
% 3.74/1.02  
% 3.74/1.02  ------ General
% 3.74/1.02  
% 3.74/1.02  abstr_ref_over_cycles:                  0
% 3.74/1.02  abstr_ref_under_cycles:                 0
% 3.74/1.02  gc_basic_clause_elim:                   0
% 3.74/1.02  forced_gc_time:                         0
% 3.74/1.02  parsing_time:                           0.012
% 3.74/1.02  unif_index_cands_time:                  0.
% 3.74/1.02  unif_index_add_time:                    0.
% 3.74/1.02  orderings_time:                         0.
% 3.74/1.02  out_proof_time:                         0.009
% 3.74/1.02  total_time:                             0.358
% 3.74/1.02  num_of_symbols:                         54
% 3.74/1.02  num_of_terms:                           8015
% 3.74/1.02  
% 3.74/1.02  ------ Preprocessing
% 3.74/1.02  
% 3.74/1.02  num_of_splits:                          0
% 3.74/1.02  num_of_split_atoms:                     0
% 3.74/1.02  num_of_reused_defs:                     0
% 3.74/1.02  num_eq_ax_congr_red:                    33
% 3.74/1.02  num_of_sem_filtered_clauses:            1
% 3.74/1.02  num_of_subtypes:                        4
% 3.74/1.02  monotx_restored_types:                  0
% 3.74/1.02  sat_num_of_epr_types:                   0
% 3.74/1.02  sat_num_of_non_cyclic_types:            0
% 3.74/1.02  sat_guarded_non_collapsed_types:        1
% 3.74/1.02  num_pure_diseq_elim:                    0
% 3.74/1.02  simp_replaced_by:                       0
% 3.74/1.02  res_preprocessed:                       92
% 3.74/1.02  prep_upred:                             0
% 3.74/1.02  prep_unflattend:                        22
% 3.74/1.02  smt_new_axioms:                         0
% 3.74/1.02  pred_elim_cands:                        5
% 3.74/1.02  pred_elim:                              5
% 3.74/1.03  pred_elim_cl:                           5
% 3.74/1.03  pred_elim_cycles:                       10
% 3.74/1.03  merged_defs:                            0
% 3.74/1.03  merged_defs_ncl:                        0
% 3.74/1.03  bin_hyper_res:                          0
% 3.74/1.03  prep_cycles:                            4
% 3.74/1.03  pred_elim_time:                         0.029
% 3.74/1.03  splitting_time:                         0.
% 3.74/1.03  sem_filter_time:                        0.
% 3.74/1.03  monotx_time:                            0.
% 3.74/1.03  subtype_inf_time:                       0.001
% 3.74/1.03  
% 3.74/1.03  ------ Problem properties
% 3.74/1.03  
% 3.74/1.03  clauses:                                18
% 3.74/1.03  conjectures:                            3
% 3.74/1.03  epr:                                    0
% 3.74/1.03  horn:                                   13
% 3.74/1.03  ground:                                 4
% 3.74/1.03  unary:                                  4
% 3.74/1.03  binary:                                 0
% 3.74/1.03  lits:                                   74
% 3.74/1.03  lits_eq:                                5
% 3.74/1.03  fd_pure:                                0
% 3.74/1.03  fd_pseudo:                              0
% 3.74/1.03  fd_cond:                                0
% 3.74/1.03  fd_pseudo_cond:                         4
% 3.74/1.03  ac_symbols:                             0
% 3.74/1.03  
% 3.74/1.03  ------ Propositional Solver
% 3.74/1.03  
% 3.74/1.03  prop_solver_calls:                      32
% 3.74/1.03  prop_fast_solver_calls:                 1259
% 3.74/1.03  smt_solver_calls:                       0
% 3.74/1.03  smt_fast_solver_calls:                  0
% 3.74/1.03  prop_num_of_clauses:                    2696
% 3.74/1.03  prop_preprocess_simplified:             8348
% 3.74/1.03  prop_fo_subsumed:                       50
% 3.74/1.03  prop_solver_time:                       0.
% 3.74/1.03  smt_solver_time:                        0.
% 3.74/1.03  smt_fast_solver_time:                   0.
% 3.74/1.03  prop_fast_solver_time:                  0.
% 3.74/1.03  prop_unsat_core_time:                   0.
% 3.74/1.03  
% 3.74/1.03  ------ QBF
% 3.74/1.03  
% 3.74/1.03  qbf_q_res:                              0
% 3.74/1.03  qbf_num_tautologies:                    0
% 3.74/1.03  qbf_prep_cycles:                        0
% 3.74/1.03  
% 3.74/1.03  ------ BMC1
% 3.74/1.03  
% 3.74/1.03  bmc1_current_bound:                     -1
% 3.74/1.03  bmc1_last_solved_bound:                 -1
% 3.74/1.03  bmc1_unsat_core_size:                   -1
% 3.74/1.03  bmc1_unsat_core_parents_size:           -1
% 3.74/1.03  bmc1_merge_next_fun:                    0
% 3.74/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.74/1.03  
% 3.74/1.03  ------ Instantiation
% 3.74/1.03  
% 3.74/1.03  inst_num_of_clauses:                    926
% 3.74/1.03  inst_num_in_passive:                    480
% 3.74/1.03  inst_num_in_active:                     433
% 3.74/1.03  inst_num_in_unprocessed:                12
% 3.74/1.03  inst_num_of_loops:                      454
% 3.74/1.03  inst_num_of_learning_restarts:          0
% 3.74/1.03  inst_num_moves_active_passive:          12
% 3.74/1.03  inst_lit_activity:                      0
% 3.74/1.03  inst_lit_activity_moves:                0
% 3.74/1.03  inst_num_tautologies:                   0
% 3.74/1.03  inst_num_prop_implied:                  0
% 3.74/1.03  inst_num_existing_simplified:           0
% 3.74/1.03  inst_num_eq_res_simplified:             0
% 3.74/1.03  inst_num_child_elim:                    0
% 3.74/1.03  inst_num_of_dismatching_blockings:      1330
% 3.74/1.03  inst_num_of_non_proper_insts:           1631
% 3.74/1.03  inst_num_of_duplicates:                 0
% 3.74/1.03  inst_inst_num_from_inst_to_res:         0
% 3.74/1.03  inst_dismatching_checking_time:         0.
% 3.74/1.03  
% 3.74/1.03  ------ Resolution
% 3.74/1.03  
% 3.74/1.03  res_num_of_clauses:                     0
% 3.74/1.03  res_num_in_passive:                     0
% 3.74/1.03  res_num_in_active:                      0
% 3.74/1.03  res_num_of_loops:                       96
% 3.74/1.03  res_forward_subset_subsumed:            42
% 3.74/1.03  res_backward_subset_subsumed:           0
% 3.74/1.03  res_forward_subsumed:                   0
% 3.74/1.03  res_backward_subsumed:                  0
% 3.74/1.03  res_forward_subsumption_resolution:     0
% 3.74/1.03  res_backward_subsumption_resolution:    0
% 3.74/1.03  res_clause_to_clause_subsumption:       677
% 3.74/1.03  res_orphan_elimination:                 0
% 3.74/1.03  res_tautology_del:                      87
% 3.74/1.03  res_num_eq_res_simplified:              0
% 3.74/1.03  res_num_sel_changes:                    0
% 3.74/1.03  res_moves_from_active_to_pass:          0
% 3.74/1.03  
% 3.74/1.03  ------ Superposition
% 3.74/1.03  
% 3.74/1.03  sup_time_total:                         0.
% 3.74/1.03  sup_time_generating:                    0.
% 3.74/1.03  sup_time_sim_full:                      0.
% 3.74/1.03  sup_time_sim_immed:                     0.
% 3.74/1.03  
% 3.74/1.03  sup_num_of_clauses:                     189
% 3.74/1.03  sup_num_in_active:                      90
% 3.74/1.03  sup_num_in_passive:                     99
% 3.74/1.03  sup_num_of_loops:                       90
% 3.74/1.03  sup_fw_superposition:                   108
% 3.74/1.03  sup_bw_superposition:                   71
% 3.74/1.03  sup_immediate_simplified:               54
% 3.74/1.03  sup_given_eliminated:                   0
% 3.74/1.03  comparisons_done:                       0
% 3.74/1.03  comparisons_avoided:                    0
% 3.74/1.03  
% 3.74/1.03  ------ Simplifications
% 3.74/1.03  
% 3.74/1.03  
% 3.74/1.03  sim_fw_subset_subsumed:                 0
% 3.74/1.03  sim_bw_subset_subsumed:                 0
% 3.74/1.03  sim_fw_subsumed:                        0
% 3.74/1.03  sim_bw_subsumed:                        0
% 3.74/1.03  sim_fw_subsumption_res:                 0
% 3.74/1.03  sim_bw_subsumption_res:                 0
% 3.74/1.03  sim_tautology_del:                      4
% 3.74/1.03  sim_eq_tautology_del:                   0
% 3.74/1.03  sim_eq_res_simp:                        0
% 3.74/1.03  sim_fw_demodulated:                     8
% 3.74/1.03  sim_bw_demodulated:                     0
% 3.74/1.03  sim_light_normalised:                   46
% 3.74/1.03  sim_joinable_taut:                      0
% 3.74/1.03  sim_joinable_simp:                      0
% 3.74/1.03  sim_ac_normalised:                      0
% 3.74/1.03  sim_smt_subsumption:                    0
% 3.74/1.03  
%------------------------------------------------------------------------------
