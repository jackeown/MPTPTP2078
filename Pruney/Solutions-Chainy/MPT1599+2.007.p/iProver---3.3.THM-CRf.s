%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:08 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 380 expanded)
%              Number of clauses        :   73 ( 137 expanded)
%              Number of leaves         :   14 (  87 expanded)
%              Depth                    :   26
%              Number of atoms          :  623 (1631 expanded)
%              Number of equality atoms :  114 ( 216 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f41,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v2_lattice3(k2_yellow_1(sK1))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f40,f39,f38])).

fof(f63,plain,(
    v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f54,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f56,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_906,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_907,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
    inference(unflattening,[status(thm)],[c_906])).

cnf(c_11,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_140,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_3])).

cnf(c_141,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_13,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_816,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_141,c_13])).

cnf(c_817,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_819,plain,
    ( ~ v2_lattice3(k2_yellow_1(X0))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_12])).

cnf(c_820,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_819])).

cnf(c_927,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_907,c_820])).

cnf(c_1043,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_23,c_927])).

cnf(c_1752,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1043])).

cnf(c_17,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1784,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1752,c_17])).

cnf(c_2075,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,X1),X0) = iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1784])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_382,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_383,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_387,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_12])).

cnf(c_388,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_387])).

cnf(c_896,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_897,plain,
    ( ~ v2_lattice3(k2_yellow_1(X0))
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_1058,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_23,c_897])).

cnf(c_1269,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution,[status(thm)],[c_388,c_1058])).

cnf(c_19,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_300,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_301,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_1321,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X3,X4)
    | X3 != X1
    | X4 != X2
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_1269,c_301])).

cnf(c_1322,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X1,X2)
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_1321])).

cnf(c_1746,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_1818,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1746,c_17])).

cnf(c_1819,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1818,c_17])).

cnf(c_3639,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0,X1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1819])).

cnf(c_4324,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),X0,X1),sK1) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2075,c_3639])).

cnf(c_1754,plain,
    ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_1777,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1754,c_17])).

cnf(c_6204,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4324,c_1777])).

cnf(c_10,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_147,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_3])).

cnf(c_148,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_789,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_148,c_13])).

cnf(c_790,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_794,plain,
    ( ~ v2_lattice3(k2_yellow_1(X0))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_12])).

cnf(c_795,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_794])).

cnf(c_928,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_907,c_795])).

cnf(c_1026,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_23,c_928])).

cnf(c_1753,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_1793,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1753,c_17])).

cnf(c_2104,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,X1),X1) = iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1793])).

cnf(c_4325,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),X0,X1),sK1) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2104,c_3639])).

cnf(c_6213,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4325,c_1777])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1758,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1757,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2366,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_1757])).

cnf(c_6215,plain,
    ( m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6213,c_2366])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1755,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1763,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1755,c_17])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1756,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1766,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1756,c_17])).

cnf(c_6522,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6215,c_1763,c_1766])).

cnf(c_6527,plain,
    ( m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6204,c_6522])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6527,c_1766,c_1763])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.43/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/0.99  
% 2.43/0.99  ------  iProver source info
% 2.43/0.99  
% 2.43/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.43/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/0.99  git: non_committed_changes: false
% 2.43/0.99  git: last_make_outside_of_git: false
% 2.43/0.99  
% 2.43/0.99  ------ 
% 2.43/0.99  
% 2.43/0.99  ------ Input Options
% 2.43/0.99  
% 2.43/0.99  --out_options                           all
% 2.43/0.99  --tptp_safe_out                         true
% 2.43/0.99  --problem_path                          ""
% 2.43/0.99  --include_path                          ""
% 2.43/0.99  --clausifier                            res/vclausify_rel
% 2.43/0.99  --clausifier_options                    --mode clausify
% 2.43/0.99  --stdin                                 false
% 2.43/0.99  --stats_out                             all
% 2.43/0.99  
% 2.43/0.99  ------ General Options
% 2.43/0.99  
% 2.43/0.99  --fof                                   false
% 2.43/0.99  --time_out_real                         305.
% 2.43/0.99  --time_out_virtual                      -1.
% 2.43/0.99  --symbol_type_check                     false
% 2.43/0.99  --clausify_out                          false
% 2.43/0.99  --sig_cnt_out                           false
% 2.43/0.99  --trig_cnt_out                          false
% 2.43/0.99  --trig_cnt_out_tolerance                1.
% 2.43/0.99  --trig_cnt_out_sk_spl                   false
% 2.43/0.99  --abstr_cl_out                          false
% 2.43/0.99  
% 2.43/0.99  ------ Global Options
% 2.43/0.99  
% 2.43/0.99  --schedule                              default
% 2.43/0.99  --add_important_lit                     false
% 2.43/0.99  --prop_solver_per_cl                    1000
% 2.43/0.99  --min_unsat_core                        false
% 2.43/0.99  --soft_assumptions                      false
% 2.43/0.99  --soft_lemma_size                       3
% 2.43/0.99  --prop_impl_unit_size                   0
% 2.43/0.99  --prop_impl_unit                        []
% 2.43/0.99  --share_sel_clauses                     true
% 2.43/0.99  --reset_solvers                         false
% 2.43/0.99  --bc_imp_inh                            [conj_cone]
% 2.43/0.99  --conj_cone_tolerance                   3.
% 2.43/0.99  --extra_neg_conj                        none
% 2.43/0.99  --large_theory_mode                     true
% 2.43/0.99  --prolific_symb_bound                   200
% 2.43/0.99  --lt_threshold                          2000
% 2.43/0.99  --clause_weak_htbl                      true
% 2.43/0.99  --gc_record_bc_elim                     false
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing Options
% 2.43/0.99  
% 2.43/0.99  --preprocessing_flag                    true
% 2.43/0.99  --time_out_prep_mult                    0.1
% 2.43/0.99  --splitting_mode                        input
% 2.43/0.99  --splitting_grd                         true
% 2.43/0.99  --splitting_cvd                         false
% 2.43/0.99  --splitting_cvd_svl                     false
% 2.43/0.99  --splitting_nvd                         32
% 2.43/0.99  --sub_typing                            true
% 2.43/0.99  --prep_gs_sim                           true
% 2.43/0.99  --prep_unflatten                        true
% 2.43/0.99  --prep_res_sim                          true
% 2.43/0.99  --prep_upred                            true
% 2.43/0.99  --prep_sem_filter                       exhaustive
% 2.43/0.99  --prep_sem_filter_out                   false
% 2.43/0.99  --pred_elim                             true
% 2.43/0.99  --res_sim_input                         true
% 2.43/0.99  --eq_ax_congr_red                       true
% 2.43/0.99  --pure_diseq_elim                       true
% 2.43/0.99  --brand_transform                       false
% 2.43/0.99  --non_eq_to_eq                          false
% 2.43/0.99  --prep_def_merge                        true
% 2.43/0.99  --prep_def_merge_prop_impl              false
% 2.43/0.99  --prep_def_merge_mbd                    true
% 2.43/0.99  --prep_def_merge_tr_red                 false
% 2.43/0.99  --prep_def_merge_tr_cl                  false
% 2.43/0.99  --smt_preprocessing                     true
% 2.43/0.99  --smt_ac_axioms                         fast
% 2.43/0.99  --preprocessed_out                      false
% 2.43/0.99  --preprocessed_stats                    false
% 2.43/0.99  
% 2.43/0.99  ------ Abstraction refinement Options
% 2.43/0.99  
% 2.43/0.99  --abstr_ref                             []
% 2.43/0.99  --abstr_ref_prep                        false
% 2.43/0.99  --abstr_ref_until_sat                   false
% 2.43/0.99  --abstr_ref_sig_restrict                funpre
% 2.43/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.99  --abstr_ref_under                       []
% 2.43/0.99  
% 2.43/0.99  ------ SAT Options
% 2.43/0.99  
% 2.43/0.99  --sat_mode                              false
% 2.43/0.99  --sat_fm_restart_options                ""
% 2.43/0.99  --sat_gr_def                            false
% 2.43/0.99  --sat_epr_types                         true
% 2.43/0.99  --sat_non_cyclic_types                  false
% 2.43/0.99  --sat_finite_models                     false
% 2.43/0.99  --sat_fm_lemmas                         false
% 2.43/0.99  --sat_fm_prep                           false
% 2.43/0.99  --sat_fm_uc_incr                        true
% 2.43/0.99  --sat_out_model                         small
% 2.43/0.99  --sat_out_clauses                       false
% 2.43/0.99  
% 2.43/0.99  ------ QBF Options
% 2.43/0.99  
% 2.43/0.99  --qbf_mode                              false
% 2.43/0.99  --qbf_elim_univ                         false
% 2.43/0.99  --qbf_dom_inst                          none
% 2.43/0.99  --qbf_dom_pre_inst                      false
% 2.43/0.99  --qbf_sk_in                             false
% 2.43/0.99  --qbf_pred_elim                         true
% 2.43/0.99  --qbf_split                             512
% 2.43/0.99  
% 2.43/0.99  ------ BMC1 Options
% 2.43/0.99  
% 2.43/0.99  --bmc1_incremental                      false
% 2.43/0.99  --bmc1_axioms                           reachable_all
% 2.43/0.99  --bmc1_min_bound                        0
% 2.43/0.99  --bmc1_max_bound                        -1
% 2.43/0.99  --bmc1_max_bound_default                -1
% 2.43/0.99  --bmc1_symbol_reachability              true
% 2.43/0.99  --bmc1_property_lemmas                  false
% 2.43/0.99  --bmc1_k_induction                      false
% 2.43/0.99  --bmc1_non_equiv_states                 false
% 2.43/0.99  --bmc1_deadlock                         false
% 2.43/0.99  --bmc1_ucm                              false
% 2.43/0.99  --bmc1_add_unsat_core                   none
% 2.43/0.99  --bmc1_unsat_core_children              false
% 2.43/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.99  --bmc1_out_stat                         full
% 2.43/0.99  --bmc1_ground_init                      false
% 2.43/0.99  --bmc1_pre_inst_next_state              false
% 2.43/0.99  --bmc1_pre_inst_state                   false
% 2.43/0.99  --bmc1_pre_inst_reach_state             false
% 2.43/0.99  --bmc1_out_unsat_core                   false
% 2.43/0.99  --bmc1_aig_witness_out                  false
% 2.43/0.99  --bmc1_verbose                          false
% 2.43/0.99  --bmc1_dump_clauses_tptp                false
% 2.43/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.99  --bmc1_dump_file                        -
% 2.43/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.99  --bmc1_ucm_extend_mode                  1
% 2.43/0.99  --bmc1_ucm_init_mode                    2
% 2.43/0.99  --bmc1_ucm_cone_mode                    none
% 2.43/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.99  --bmc1_ucm_relax_model                  4
% 2.43/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.99  --bmc1_ucm_layered_model                none
% 2.43/0.99  --bmc1_ucm_max_lemma_size               10
% 2.43/0.99  
% 2.43/0.99  ------ AIG Options
% 2.43/0.99  
% 2.43/0.99  --aig_mode                              false
% 2.43/0.99  
% 2.43/0.99  ------ Instantiation Options
% 2.43/0.99  
% 2.43/0.99  --instantiation_flag                    true
% 2.43/0.99  --inst_sos_flag                         false
% 2.43/0.99  --inst_sos_phase                        true
% 2.43/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.99  --inst_lit_sel_side                     num_symb
% 2.43/0.99  --inst_solver_per_active                1400
% 2.43/0.99  --inst_solver_calls_frac                1.
% 2.43/0.99  --inst_passive_queue_type               priority_queues
% 2.43/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.99  --inst_passive_queues_freq              [25;2]
% 2.43/0.99  --inst_dismatching                      true
% 2.43/0.99  --inst_eager_unprocessed_to_passive     true
% 2.43/0.99  --inst_prop_sim_given                   true
% 2.43/0.99  --inst_prop_sim_new                     false
% 2.43/0.99  --inst_subs_new                         false
% 2.43/0.99  --inst_eq_res_simp                      false
% 2.43/0.99  --inst_subs_given                       false
% 2.43/0.99  --inst_orphan_elimination               true
% 2.43/0.99  --inst_learning_loop_flag               true
% 2.43/0.99  --inst_learning_start                   3000
% 2.43/0.99  --inst_learning_factor                  2
% 2.43/0.99  --inst_start_prop_sim_after_learn       3
% 2.43/0.99  --inst_sel_renew                        solver
% 2.43/0.99  --inst_lit_activity_flag                true
% 2.43/0.99  --inst_restr_to_given                   false
% 2.43/0.99  --inst_activity_threshold               500
% 2.43/0.99  --inst_out_proof                        true
% 2.43/0.99  
% 2.43/0.99  ------ Resolution Options
% 2.43/0.99  
% 2.43/0.99  --resolution_flag                       true
% 2.43/0.99  --res_lit_sel                           adaptive
% 2.43/0.99  --res_lit_sel_side                      none
% 2.43/0.99  --res_ordering                          kbo
% 2.43/0.99  --res_to_prop_solver                    active
% 2.43/0.99  --res_prop_simpl_new                    false
% 2.43/0.99  --res_prop_simpl_given                  true
% 2.43/0.99  --res_passive_queue_type                priority_queues
% 2.43/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.99  --res_passive_queues_freq               [15;5]
% 2.43/0.99  --res_forward_subs                      full
% 2.43/0.99  --res_backward_subs                     full
% 2.43/0.99  --res_forward_subs_resolution           true
% 2.43/0.99  --res_backward_subs_resolution          true
% 2.43/0.99  --res_orphan_elimination                true
% 2.43/0.99  --res_time_limit                        2.
% 2.43/0.99  --res_out_proof                         true
% 2.43/0.99  
% 2.43/0.99  ------ Superposition Options
% 2.43/0.99  
% 2.43/0.99  --superposition_flag                    true
% 2.43/0.99  --sup_passive_queue_type                priority_queues
% 2.43/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.99  --demod_completeness_check              fast
% 2.43/0.99  --demod_use_ground                      true
% 2.43/0.99  --sup_to_prop_solver                    passive
% 2.43/0.99  --sup_prop_simpl_new                    true
% 2.43/0.99  --sup_prop_simpl_given                  true
% 2.43/0.99  --sup_fun_splitting                     false
% 2.43/0.99  --sup_smt_interval                      50000
% 2.43/0.99  
% 2.43/0.99  ------ Superposition Simplification Setup
% 2.43/0.99  
% 2.43/0.99  --sup_indices_passive                   []
% 2.43/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_full_bw                           [BwDemod]
% 2.43/0.99  --sup_immed_triv                        [TrivRules]
% 2.43/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_immed_bw_main                     []
% 2.43/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.99  
% 2.43/0.99  ------ Combination Options
% 2.43/0.99  
% 2.43/0.99  --comb_res_mult                         3
% 2.43/0.99  --comb_sup_mult                         2
% 2.43/0.99  --comb_inst_mult                        10
% 2.43/0.99  
% 2.43/0.99  ------ Debug Options
% 2.43/0.99  
% 2.43/0.99  --dbg_backtrace                         false
% 2.43/0.99  --dbg_dump_prop_clauses                 false
% 2.43/0.99  --dbg_dump_prop_clauses_file            -
% 2.43/0.99  --dbg_out_stat                          false
% 2.43/0.99  ------ Parsing...
% 2.43/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/0.99  ------ Proving...
% 2.43/0.99  ------ Problem Properties 
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  clauses                                 16
% 2.43/0.99  conjectures                             3
% 2.43/0.99  EPR                                     0
% 2.43/0.99  Horn                                    13
% 2.43/0.99  unary                                   5
% 2.43/0.99  binary                                  0
% 2.43/0.99  lits                                    72
% 2.43/0.99  lits eq                                 15
% 2.43/0.99  fd_pure                                 0
% 2.43/0.99  fd_pseudo                               0
% 2.43/0.99  fd_cond                                 0
% 2.43/0.99  fd_pseudo_cond                          4
% 2.43/0.99  AC symbols                              0
% 2.43/0.99  
% 2.43/0.99  ------ Schedule dynamic 5 is on 
% 2.43/0.99  
% 2.43/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  ------ 
% 2.43/0.99  Current options:
% 2.43/0.99  ------ 
% 2.43/0.99  
% 2.43/0.99  ------ Input Options
% 2.43/0.99  
% 2.43/0.99  --out_options                           all
% 2.43/0.99  --tptp_safe_out                         true
% 2.43/0.99  --problem_path                          ""
% 2.43/0.99  --include_path                          ""
% 2.43/0.99  --clausifier                            res/vclausify_rel
% 2.43/0.99  --clausifier_options                    --mode clausify
% 2.43/0.99  --stdin                                 false
% 2.43/0.99  --stats_out                             all
% 2.43/0.99  
% 2.43/0.99  ------ General Options
% 2.43/0.99  
% 2.43/0.99  --fof                                   false
% 2.43/0.99  --time_out_real                         305.
% 2.43/0.99  --time_out_virtual                      -1.
% 2.43/0.99  --symbol_type_check                     false
% 2.43/0.99  --clausify_out                          false
% 2.43/0.99  --sig_cnt_out                           false
% 2.43/0.99  --trig_cnt_out                          false
% 2.43/0.99  --trig_cnt_out_tolerance                1.
% 2.43/0.99  --trig_cnt_out_sk_spl                   false
% 2.43/0.99  --abstr_cl_out                          false
% 2.43/0.99  
% 2.43/0.99  ------ Global Options
% 2.43/0.99  
% 2.43/0.99  --schedule                              default
% 2.43/0.99  --add_important_lit                     false
% 2.43/0.99  --prop_solver_per_cl                    1000
% 2.43/0.99  --min_unsat_core                        false
% 2.43/0.99  --soft_assumptions                      false
% 2.43/0.99  --soft_lemma_size                       3
% 2.43/0.99  --prop_impl_unit_size                   0
% 2.43/0.99  --prop_impl_unit                        []
% 2.43/0.99  --share_sel_clauses                     true
% 2.43/0.99  --reset_solvers                         false
% 2.43/0.99  --bc_imp_inh                            [conj_cone]
% 2.43/0.99  --conj_cone_tolerance                   3.
% 2.43/0.99  --extra_neg_conj                        none
% 2.43/0.99  --large_theory_mode                     true
% 2.43/0.99  --prolific_symb_bound                   200
% 2.43/0.99  --lt_threshold                          2000
% 2.43/0.99  --clause_weak_htbl                      true
% 2.43/0.99  --gc_record_bc_elim                     false
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing Options
% 2.43/0.99  
% 2.43/0.99  --preprocessing_flag                    true
% 2.43/0.99  --time_out_prep_mult                    0.1
% 2.43/0.99  --splitting_mode                        input
% 2.43/0.99  --splitting_grd                         true
% 2.43/0.99  --splitting_cvd                         false
% 2.43/0.99  --splitting_cvd_svl                     false
% 2.43/0.99  --splitting_nvd                         32
% 2.43/0.99  --sub_typing                            true
% 2.43/0.99  --prep_gs_sim                           true
% 2.43/0.99  --prep_unflatten                        true
% 2.43/0.99  --prep_res_sim                          true
% 2.43/0.99  --prep_upred                            true
% 2.43/0.99  --prep_sem_filter                       exhaustive
% 2.43/0.99  --prep_sem_filter_out                   false
% 2.43/0.99  --pred_elim                             true
% 2.43/0.99  --res_sim_input                         true
% 2.43/0.99  --eq_ax_congr_red                       true
% 2.43/0.99  --pure_diseq_elim                       true
% 2.43/0.99  --brand_transform                       false
% 2.43/0.99  --non_eq_to_eq                          false
% 2.43/0.99  --prep_def_merge                        true
% 2.43/0.99  --prep_def_merge_prop_impl              false
% 2.43/0.99  --prep_def_merge_mbd                    true
% 2.43/0.99  --prep_def_merge_tr_red                 false
% 2.43/0.99  --prep_def_merge_tr_cl                  false
% 2.43/0.99  --smt_preprocessing                     true
% 2.43/0.99  --smt_ac_axioms                         fast
% 2.43/0.99  --preprocessed_out                      false
% 2.43/0.99  --preprocessed_stats                    false
% 2.43/0.99  
% 2.43/0.99  ------ Abstraction refinement Options
% 2.43/0.99  
% 2.43/0.99  --abstr_ref                             []
% 2.43/0.99  --abstr_ref_prep                        false
% 2.43/0.99  --abstr_ref_until_sat                   false
% 2.43/0.99  --abstr_ref_sig_restrict                funpre
% 2.43/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.99  --abstr_ref_under                       []
% 2.43/0.99  
% 2.43/0.99  ------ SAT Options
% 2.43/0.99  
% 2.43/0.99  --sat_mode                              false
% 2.43/0.99  --sat_fm_restart_options                ""
% 2.43/0.99  --sat_gr_def                            false
% 2.43/0.99  --sat_epr_types                         true
% 2.43/0.99  --sat_non_cyclic_types                  false
% 2.43/0.99  --sat_finite_models                     false
% 2.43/0.99  --sat_fm_lemmas                         false
% 2.43/0.99  --sat_fm_prep                           false
% 2.43/0.99  --sat_fm_uc_incr                        true
% 2.43/0.99  --sat_out_model                         small
% 2.43/0.99  --sat_out_clauses                       false
% 2.43/0.99  
% 2.43/0.99  ------ QBF Options
% 2.43/0.99  
% 2.43/0.99  --qbf_mode                              false
% 2.43/0.99  --qbf_elim_univ                         false
% 2.43/0.99  --qbf_dom_inst                          none
% 2.43/0.99  --qbf_dom_pre_inst                      false
% 2.43/0.99  --qbf_sk_in                             false
% 2.43/0.99  --qbf_pred_elim                         true
% 2.43/0.99  --qbf_split                             512
% 2.43/0.99  
% 2.43/0.99  ------ BMC1 Options
% 2.43/0.99  
% 2.43/0.99  --bmc1_incremental                      false
% 2.43/0.99  --bmc1_axioms                           reachable_all
% 2.43/0.99  --bmc1_min_bound                        0
% 2.43/0.99  --bmc1_max_bound                        -1
% 2.43/0.99  --bmc1_max_bound_default                -1
% 2.43/0.99  --bmc1_symbol_reachability              true
% 2.43/0.99  --bmc1_property_lemmas                  false
% 2.43/0.99  --bmc1_k_induction                      false
% 2.43/0.99  --bmc1_non_equiv_states                 false
% 2.43/0.99  --bmc1_deadlock                         false
% 2.43/0.99  --bmc1_ucm                              false
% 2.43/0.99  --bmc1_add_unsat_core                   none
% 2.43/0.99  --bmc1_unsat_core_children              false
% 2.43/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.99  --bmc1_out_stat                         full
% 2.43/0.99  --bmc1_ground_init                      false
% 2.43/0.99  --bmc1_pre_inst_next_state              false
% 2.43/0.99  --bmc1_pre_inst_state                   false
% 2.43/0.99  --bmc1_pre_inst_reach_state             false
% 2.43/0.99  --bmc1_out_unsat_core                   false
% 2.43/0.99  --bmc1_aig_witness_out                  false
% 2.43/0.99  --bmc1_verbose                          false
% 2.43/0.99  --bmc1_dump_clauses_tptp                false
% 2.43/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.99  --bmc1_dump_file                        -
% 2.43/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.99  --bmc1_ucm_extend_mode                  1
% 2.43/0.99  --bmc1_ucm_init_mode                    2
% 2.43/0.99  --bmc1_ucm_cone_mode                    none
% 2.43/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.99  --bmc1_ucm_relax_model                  4
% 2.43/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.99  --bmc1_ucm_layered_model                none
% 2.43/0.99  --bmc1_ucm_max_lemma_size               10
% 2.43/0.99  
% 2.43/0.99  ------ AIG Options
% 2.43/0.99  
% 2.43/0.99  --aig_mode                              false
% 2.43/0.99  
% 2.43/0.99  ------ Instantiation Options
% 2.43/0.99  
% 2.43/0.99  --instantiation_flag                    true
% 2.43/0.99  --inst_sos_flag                         false
% 2.43/0.99  --inst_sos_phase                        true
% 2.43/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.99  --inst_lit_sel_side                     none
% 2.43/0.99  --inst_solver_per_active                1400
% 2.43/0.99  --inst_solver_calls_frac                1.
% 2.43/0.99  --inst_passive_queue_type               priority_queues
% 2.43/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.99  --inst_passive_queues_freq              [25;2]
% 2.43/0.99  --inst_dismatching                      true
% 2.43/0.99  --inst_eager_unprocessed_to_passive     true
% 2.43/0.99  --inst_prop_sim_given                   true
% 2.43/0.99  --inst_prop_sim_new                     false
% 2.43/0.99  --inst_subs_new                         false
% 2.43/0.99  --inst_eq_res_simp                      false
% 2.43/0.99  --inst_subs_given                       false
% 2.43/0.99  --inst_orphan_elimination               true
% 2.43/0.99  --inst_learning_loop_flag               true
% 2.43/0.99  --inst_learning_start                   3000
% 2.43/0.99  --inst_learning_factor                  2
% 2.43/0.99  --inst_start_prop_sim_after_learn       3
% 2.43/0.99  --inst_sel_renew                        solver
% 2.43/0.99  --inst_lit_activity_flag                true
% 2.43/0.99  --inst_restr_to_given                   false
% 2.43/0.99  --inst_activity_threshold               500
% 2.43/0.99  --inst_out_proof                        true
% 2.43/0.99  
% 2.43/0.99  ------ Resolution Options
% 2.43/0.99  
% 2.43/0.99  --resolution_flag                       false
% 2.43/0.99  --res_lit_sel                           adaptive
% 2.43/0.99  --res_lit_sel_side                      none
% 2.43/0.99  --res_ordering                          kbo
% 2.43/0.99  --res_to_prop_solver                    active
% 2.43/0.99  --res_prop_simpl_new                    false
% 2.43/0.99  --res_prop_simpl_given                  true
% 2.43/0.99  --res_passive_queue_type                priority_queues
% 2.43/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.99  --res_passive_queues_freq               [15;5]
% 2.43/0.99  --res_forward_subs                      full
% 2.43/0.99  --res_backward_subs                     full
% 2.43/0.99  --res_forward_subs_resolution           true
% 2.43/0.99  --res_backward_subs_resolution          true
% 2.43/0.99  --res_orphan_elimination                true
% 2.43/0.99  --res_time_limit                        2.
% 2.43/0.99  --res_out_proof                         true
% 2.43/0.99  
% 2.43/0.99  ------ Superposition Options
% 2.43/0.99  
% 2.43/0.99  --superposition_flag                    true
% 2.43/0.99  --sup_passive_queue_type                priority_queues
% 2.43/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.99  --demod_completeness_check              fast
% 2.43/0.99  --demod_use_ground                      true
% 2.43/0.99  --sup_to_prop_solver                    passive
% 2.43/0.99  --sup_prop_simpl_new                    true
% 2.43/0.99  --sup_prop_simpl_given                  true
% 2.43/0.99  --sup_fun_splitting                     false
% 2.43/0.99  --sup_smt_interval                      50000
% 2.43/0.99  
% 2.43/0.99  ------ Superposition Simplification Setup
% 2.43/0.99  
% 2.43/0.99  --sup_indices_passive                   []
% 2.43/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_full_bw                           [BwDemod]
% 2.43/0.99  --sup_immed_triv                        [TrivRules]
% 2.43/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_immed_bw_main                     []
% 2.43/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.99  
% 2.43/0.99  ------ Combination Options
% 2.43/0.99  
% 2.43/0.99  --comb_res_mult                         3
% 2.43/0.99  --comb_sup_mult                         2
% 2.43/0.99  --comb_inst_mult                        10
% 2.43/0.99  
% 2.43/0.99  ------ Debug Options
% 2.43/0.99  
% 2.43/0.99  --dbg_backtrace                         false
% 2.43/0.99  --dbg_dump_prop_clauses                 false
% 2.43/0.99  --dbg_dump_prop_clauses_file            -
% 2.43/0.99  --dbg_out_stat                          false
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  ------ Proving...
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  % SZS status Theorem for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  fof(f11,conjecture,(
% 2.43/0.99    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f12,negated_conjecture,(
% 2.43/0.99    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.43/0.99    inference(negated_conjecture,[],[f11])).
% 2.43/0.99  
% 2.43/0.99  fof(f29,plain,(
% 2.43/0.99    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 2.43/0.99    inference(ennf_transformation,[],[f12])).
% 2.43/0.99  
% 2.43/0.99  fof(f30,plain,(
% 2.43/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 2.43/0.99    inference(flattening,[],[f29])).
% 2.43/0.99  
% 2.43/0.99  fof(f40,plain,(
% 2.43/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f39,plain,(
% 2.43/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),sK2,X2),k3_xboole_0(sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f38,plain,(
% 2.43/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f41,plain,(
% 2.43/0.99    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 2.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f40,f39,f38])).
% 2.43/0.99  
% 2.43/0.99  fof(f63,plain,(
% 2.43/0.99    v2_lattice3(k2_yellow_1(sK1))),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  fof(f4,axiom,(
% 2.43/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f23,plain,(
% 2.43/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f4])).
% 2.43/0.99  
% 2.43/0.99  fof(f24,plain,(
% 2.43/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(flattening,[],[f23])).
% 2.43/0.99  
% 2.43/0.99  fof(f46,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f24])).
% 2.43/0.99  
% 2.43/0.99  fof(f6,axiom,(
% 2.43/0.99    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f14,plain,(
% 2.43/0.99    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.43/0.99    inference(pure_predicate_removal,[],[f6])).
% 2.43/0.99  
% 2.43/0.99  fof(f54,plain,(
% 2.43/0.99    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.43/0.99    inference(cnf_transformation,[],[f14])).
% 2.43/0.99  
% 2.43/0.99  fof(f5,axiom,(
% 2.43/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f25,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f5])).
% 2.43/0.99  
% 2.43/0.99  fof(f26,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(flattening,[],[f25])).
% 2.43/0.99  
% 2.43/0.99  fof(f32,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(nnf_transformation,[],[f26])).
% 2.43/0.99  
% 2.43/0.99  fof(f33,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(flattening,[],[f32])).
% 2.43/0.99  
% 2.43/0.99  fof(f34,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(rectify,[],[f33])).
% 2.43/0.99  
% 2.43/0.99  fof(f35,plain,(
% 2.43/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f36,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.43/0.99  
% 2.43/0.99  fof(f47,plain,(
% 2.43/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f36])).
% 2.43/0.99  
% 2.43/0.99  fof(f69,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(equality_resolution,[],[f47])).
% 2.43/0.99  
% 2.43/0.99  fof(f3,axiom,(
% 2.43/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f21,plain,(
% 2.43/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(ennf_transformation,[],[f3])).
% 2.43/0.99  
% 2.43/0.99  fof(f22,plain,(
% 2.43/0.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(flattening,[],[f21])).
% 2.43/0.99  
% 2.43/0.99  fof(f45,plain,(
% 2.43/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f22])).
% 2.43/0.99  
% 2.43/0.99  fof(f7,axiom,(
% 2.43/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f13,plain,(
% 2.43/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.43/0.99    inference(pure_predicate_removal,[],[f7])).
% 2.43/0.99  
% 2.43/0.99  fof(f16,plain,(
% 2.43/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.43/0.99    inference(pure_predicate_removal,[],[f13])).
% 2.43/0.99  
% 2.43/0.99  fof(f56,plain,(
% 2.43/0.99    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.43/0.99    inference(cnf_transformation,[],[f16])).
% 2.43/0.99  
% 2.43/0.99  fof(f9,axiom,(
% 2.43/0.99    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f58,plain,(
% 2.43/0.99    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.43/0.99    inference(cnf_transformation,[],[f9])).
% 2.43/0.99  
% 2.43/0.99  fof(f2,axiom,(
% 2.43/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f19,plain,(
% 2.43/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f2])).
% 2.43/0.99  
% 2.43/0.99  fof(f20,plain,(
% 2.43/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(flattening,[],[f19])).
% 2.43/0.99  
% 2.43/0.99  fof(f31,plain,(
% 2.43/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(nnf_transformation,[],[f20])).
% 2.43/0.99  
% 2.43/0.99  fof(f44,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f31])).
% 2.43/0.99  
% 2.43/0.99  fof(f55,plain,(
% 2.43/0.99    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.43/0.99    inference(cnf_transformation,[],[f16])).
% 2.43/0.99  
% 2.43/0.99  fof(f10,axiom,(
% 2.43/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f28,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.43/0.99    inference(ennf_transformation,[],[f10])).
% 2.43/0.99  
% 2.43/0.99  fof(f37,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.43/0.99    inference(nnf_transformation,[],[f28])).
% 2.43/0.99  
% 2.43/0.99  fof(f60,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f37])).
% 2.43/0.99  
% 2.43/0.99  fof(f62,plain,(
% 2.43/0.99    ~v1_xboole_0(sK1)),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  fof(f48,plain,(
% 2.43/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f36])).
% 2.43/0.99  
% 2.43/0.99  fof(f68,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(equality_resolution,[],[f48])).
% 2.43/0.99  
% 2.43/0.99  fof(f1,axiom,(
% 2.43/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f17,plain,(
% 2.43/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.43/0.99    inference(ennf_transformation,[],[f1])).
% 2.43/0.99  
% 2.43/0.99  fof(f18,plain,(
% 2.43/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.43/0.99    inference(flattening,[],[f17])).
% 2.43/0.99  
% 2.43/0.99  fof(f42,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f18])).
% 2.43/0.99  
% 2.43/0.99  fof(f66,plain,(
% 2.43/0.99    ~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  fof(f64,plain,(
% 2.43/0.99    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  fof(f65,plain,(
% 2.43/0.99    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  cnf(c_23,negated_conjecture,
% 2.43/0.99      ( v2_lattice3(k2_yellow_1(sK1)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.43/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.43/0.99      | ~ l1_orders_2(X1) ),
% 2.43/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_12,plain,
% 2.43/0.99      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_906,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.43/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.43/0.99      | k2_yellow_1(X3) != X1 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_12]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_907,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.43/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_906]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_11,plain,
% 2.43/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ v2_lattice3(X0)
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3,plain,
% 2.43/0.99      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_140,plain,
% 2.43/0.99      ( ~ v2_lattice3(X0)
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_11,c_3]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_141,plain,
% 2.43/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ v2_lattice3(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_140]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_13,plain,
% 2.43/0.99      ( v5_orders_2(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_816,plain,
% 2.43/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ v2_lattice3(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k2_yellow_1(X3) != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_141,c_13]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_817,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ v2_lattice3(k2_yellow_1(X0))
% 2.43/0.99      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_816]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_819,plain,
% 2.43/0.99      ( ~ v2_lattice3(k2_yellow_1(X0))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_817,c_12]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_820,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_819]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_927,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(backward_subsumption_resolution,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_907,c_820]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1043,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_927]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1752,plain,
% 2.43/0.99      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) = iProver_top
% 2.43/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1043]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_17,plain,
% 2.43/0.99      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.43/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1784,plain,
% 2.43/0.99      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) = iProver_top
% 2.43/0.99      | m1_subset_1(X2,X0) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,X0) != iProver_top ),
% 2.43/0.99      inference(light_normalisation,[status(thm)],[c_1752,c_17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2075,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,X1),X0) = iProver_top
% 2.43/0.99      | m1_subset_1(X1,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.43/0.99      inference(equality_resolution,[status(thm)],[c_1784]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1,plain,
% 2.43/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.43/0.99      | r3_orders_2(X0,X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ v3_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_14,plain,
% 2.43/0.99      ( v3_orders_2(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_382,plain,
% 2.43/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.43/0.99      | r3_orders_2(X0,X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k2_yellow_1(X3) != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_383,plain,
% 2.43/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | v2_struct_0(k2_yellow_1(X0))
% 2.43/0.99      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_382]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_387,plain,
% 2.43/0.99      ( v2_struct_0(k2_yellow_1(X0))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_383,c_12]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_388,plain,
% 2.43/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_387]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_896,plain,
% 2.43/0.99      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | k2_yellow_1(X1) != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_897,plain,
% 2.43/0.99      ( ~ v2_lattice3(k2_yellow_1(X0)) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_896]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1058,plain,
% 2.43/0.99      ( ~ v2_struct_0(k2_yellow_1(X0))
% 2.43/0.99      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_897]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1269,plain,
% 2.43/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.43/0.99      inference(resolution,[status(thm)],[c_388,c_1058]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_19,plain,
% 2.43/0.99      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | r1_tarski(X1,X2)
% 2.43/0.99      | v1_xboole_0(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_24,negated_conjecture,
% 2.43/0.99      ( ~ v1_xboole_0(sK1) ),
% 2.43/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_300,plain,
% 2.43/0.99      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | r1_tarski(X1,X2)
% 2.43/0.99      | sK1 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_301,plain,
% 2.43/0.99      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.43/0.99      | r1_tarski(X0,X1) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_300]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1321,plain,
% 2.43/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
% 2.43/0.99      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK1)))
% 2.43/0.99      | r1_tarski(X3,X4)
% 2.43/0.99      | X3 != X1
% 2.43/0.99      | X4 != X2
% 2.43/0.99      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_1269,c_301]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1322,plain,
% 2.43/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
% 2.43/0.99      | r1_tarski(X1,X2)
% 2.43/0.99      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1321]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1746,plain,
% 2.43/0.99      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.43/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.43/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.43/0.99      | r1_tarski(X1,X2) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1818,plain,
% 2.43/0.99      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.43/0.99      | m1_subset_1(X2,X0) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,X0) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.43/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.43/0.99      | r1_tarski(X1,X2) = iProver_top ),
% 2.43/0.99      inference(light_normalisation,[status(thm)],[c_1746,c_17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1819,plain,
% 2.43/0.99      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.43/0.99      | m1_subset_1(X2,X0) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,X0) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 2.43/0.99      | r1_tarski(X1,X2) = iProver_top ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_1818,c_17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3639,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(sK1),X0,X1) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 2.43/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.43/0.99      inference(equality_resolution,[status(thm)],[c_1819]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4324,plain,
% 2.43/0.99      ( m1_subset_1(X0,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),X0,X1),sK1) != iProver_top
% 2.43/0.99      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X0,X1),X0) = iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_2075,c_3639]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1754,plain,
% 2.43/0.99      ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 2.43/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 2.43/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1777,plain,
% 2.43/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.43/0.99      | m1_subset_1(X2,X1) != iProver_top
% 2.43/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) = iProver_top ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_1754,c_17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_6204,plain,
% 2.43/0.99      ( m1_subset_1(X0,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,sK1) != iProver_top
% 2.43/0.99      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X0),X1) = iProver_top ),
% 2.43/0.99      inference(forward_subsumption_resolution,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_4324,c_1777]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_10,plain,
% 2.43/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ v2_lattice3(X0)
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_147,plain,
% 2.43/0.99      ( ~ v2_lattice3(X0)
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_10,c_3]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_148,plain,
% 2.43/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ v2_lattice3(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_147]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_789,plain,
% 2.43/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ v2_lattice3(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k2_yellow_1(X3) != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_148,c_13]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_790,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ v2_lattice3(k2_yellow_1(X0))
% 2.43/0.99      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_789]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_794,plain,
% 2.43/0.99      ( ~ v2_lattice3(k2_yellow_1(X0))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_790,c_12]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_795,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_794]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_928,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.43/0.99      inference(backward_subsumption_resolution,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_907,c_795]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1026,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.43/0.99      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_928]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1753,plain,
% 2.43/0.99      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2) = iProver_top
% 2.43/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1793,plain,
% 2.43/0.99      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.43/0.99      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2) = iProver_top
% 2.43/0.99      | m1_subset_1(X2,X0) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,X0) != iProver_top ),
% 2.43/0.99      inference(light_normalisation,[status(thm)],[c_1753,c_17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2104,plain,
% 2.43/0.99      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,X1),X1) = iProver_top
% 2.43/0.99      | m1_subset_1(X1,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.43/0.99      inference(equality_resolution,[status(thm)],[c_1793]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4325,plain,
% 2.43/0.99      ( m1_subset_1(X0,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),X0,X1),sK1) != iProver_top
% 2.43/0.99      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X0,X1),X1) = iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_2104,c_3639]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_6213,plain,
% 2.43/0.99      ( m1_subset_1(X0,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(X1,sK1) != iProver_top
% 2.43/0.99      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X0),X0) = iProver_top ),
% 2.43/0.99      inference(forward_subsumption_resolution,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_4325,c_1777]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_0,plain,
% 2.43/0.99      ( ~ r1_tarski(X0,X1)
% 2.43/0.99      | ~ r1_tarski(X0,X2)
% 2.43/0.99      | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1758,plain,
% 2.43/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.43/0.99      | r1_tarski(X0,X2) != iProver_top
% 2.43/0.99      | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_20,negated_conjecture,
% 2.43/0.99      ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1757,plain,
% 2.43/0.99      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2366,plain,
% 2.43/0.99      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
% 2.43/0.99      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1758,c_1757]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_6215,plain,
% 2.43/0.99      ( m1_subset_1(sK3,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(sK2,sK1) != iProver_top
% 2.43/0.99      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_6213,c_2366]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_22,negated_conjecture,
% 2.43/0.99      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.43/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1755,plain,
% 2.43/0.99      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1763,plain,
% 2.43/0.99      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_1755,c_17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_21,negated_conjecture,
% 2.43/0.99      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.43/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1756,plain,
% 2.43/0.99      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1766,plain,
% 2.43/0.99      ( m1_subset_1(sK3,sK1) = iProver_top ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_1756,c_17]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_6522,plain,
% 2.43/0.99      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_6215,c_1763,c_1766]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_6527,plain,
% 2.43/0.99      ( m1_subset_1(sK3,sK1) != iProver_top
% 2.43/0.99      | m1_subset_1(sK2,sK1) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_6204,c_6522]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(contradiction,plain,
% 2.43/0.99      ( $false ),
% 2.43/0.99      inference(minisat,[status(thm)],[c_6527,c_1766,c_1763]) ).
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  ------                               Statistics
% 2.43/0.99  
% 2.43/0.99  ------ General
% 2.43/0.99  
% 2.43/0.99  abstr_ref_over_cycles:                  0
% 2.43/0.99  abstr_ref_under_cycles:                 0
% 2.43/0.99  gc_basic_clause_elim:                   0
% 2.43/0.99  forced_gc_time:                         0
% 2.43/0.99  parsing_time:                           0.012
% 2.43/0.99  unif_index_cands_time:                  0.
% 2.43/0.99  unif_index_add_time:                    0.
% 2.43/0.99  orderings_time:                         0.
% 2.43/0.99  out_proof_time:                         0.01
% 2.43/0.99  total_time:                             0.263
% 2.43/0.99  num_of_symbols:                         51
% 2.43/0.99  num_of_terms:                           8481
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing
% 2.43/0.99  
% 2.43/0.99  num_of_splits:                          0
% 2.43/0.99  num_of_split_atoms:                     0
% 2.43/0.99  num_of_reused_defs:                     0
% 2.43/0.99  num_eq_ax_congr_red:                    16
% 2.43/0.99  num_of_sem_filtered_clauses:            1
% 2.43/0.99  num_of_subtypes:                        0
% 2.43/0.99  monotx_restored_types:                  0
% 2.43/0.99  sat_num_of_epr_types:                   0
% 2.43/0.99  sat_num_of_non_cyclic_types:            0
% 2.43/0.99  sat_guarded_non_collapsed_types:        0
% 2.43/0.99  num_pure_diseq_elim:                    0
% 2.43/0.99  simp_replaced_by:                       0
% 2.43/0.99  res_preprocessed:                       96
% 2.43/0.99  prep_upred:                             0
% 2.43/0.99  prep_unflattend:                        24
% 2.43/0.99  smt_new_axioms:                         0
% 2.43/0.99  pred_elim_cands:                        3
% 2.43/0.99  pred_elim:                              7
% 2.43/0.99  pred_elim_cl:                           9
% 2.43/0.99  pred_elim_cycles:                       12
% 2.43/0.99  merged_defs:                            0
% 2.43/0.99  merged_defs_ncl:                        0
% 2.43/0.99  bin_hyper_res:                          0
% 2.43/0.99  prep_cycles:                            4
% 2.43/0.99  pred_elim_time:                         0.021
% 2.43/0.99  splitting_time:                         0.
% 2.43/0.99  sem_filter_time:                        0.
% 2.43/0.99  monotx_time:                            0.
% 2.43/0.99  subtype_inf_time:                       0.
% 2.43/0.99  
% 2.43/0.99  ------ Problem properties
% 2.43/0.99  
% 2.43/0.99  clauses:                                16
% 2.43/0.99  conjectures:                            3
% 2.43/0.99  epr:                                    0
% 2.43/0.99  horn:                                   13
% 2.43/0.99  ground:                                 3
% 2.43/0.99  unary:                                  5
% 2.43/0.99  binary:                                 0
% 2.43/0.99  lits:                                   72
% 2.43/0.99  lits_eq:                                15
% 2.43/0.99  fd_pure:                                0
% 2.43/0.99  fd_pseudo:                              0
% 2.43/0.99  fd_cond:                                0
% 2.43/0.99  fd_pseudo_cond:                         4
% 2.43/0.99  ac_symbols:                             0
% 2.43/0.99  
% 2.43/0.99  ------ Propositional Solver
% 2.43/0.99  
% 2.43/0.99  prop_solver_calls:                      26
% 2.43/0.99  prop_fast_solver_calls:                 1278
% 2.43/0.99  smt_solver_calls:                       0
% 2.43/0.99  smt_fast_solver_calls:                  0
% 2.43/0.99  prop_num_of_clauses:                    3228
% 2.43/0.99  prop_preprocess_simplified:             7344
% 2.43/0.99  prop_fo_subsumed:                       20
% 2.43/0.99  prop_solver_time:                       0.
% 2.43/0.99  smt_solver_time:                        0.
% 2.43/0.99  smt_fast_solver_time:                   0.
% 2.43/0.99  prop_fast_solver_time:                  0.
% 2.43/0.99  prop_unsat_core_time:                   0.
% 2.43/0.99  
% 2.43/0.99  ------ QBF
% 2.43/0.99  
% 2.43/0.99  qbf_q_res:                              0
% 2.43/0.99  qbf_num_tautologies:                    0
% 2.43/0.99  qbf_prep_cycles:                        0
% 2.43/0.99  
% 2.43/0.99  ------ BMC1
% 2.43/0.99  
% 2.43/0.99  bmc1_current_bound:                     -1
% 2.43/0.99  bmc1_last_solved_bound:                 -1
% 2.43/0.99  bmc1_unsat_core_size:                   -1
% 2.43/0.99  bmc1_unsat_core_parents_size:           -1
% 2.43/0.99  bmc1_merge_next_fun:                    0
% 2.43/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.43/0.99  
% 2.43/0.99  ------ Instantiation
% 2.43/0.99  
% 2.43/0.99  inst_num_of_clauses:                    829
% 2.43/0.99  inst_num_in_passive:                    454
% 2.43/0.99  inst_num_in_active:                     145
% 2.43/0.99  inst_num_in_unprocessed:                230
% 2.43/0.99  inst_num_of_loops:                      150
% 2.43/0.99  inst_num_of_learning_restarts:          0
% 2.43/0.99  inst_num_moves_active_passive:          3
% 2.43/0.99  inst_lit_activity:                      0
% 2.43/0.99  inst_lit_activity_moves:                0
% 2.43/0.99  inst_num_tautologies:                   0
% 2.43/0.99  inst_num_prop_implied:                  0
% 2.43/0.99  inst_num_existing_simplified:           0
% 2.43/0.99  inst_num_eq_res_simplified:             0
% 2.43/0.99  inst_num_child_elim:                    0
% 2.43/0.99  inst_num_of_dismatching_blockings:      91
% 2.43/0.99  inst_num_of_non_proper_insts:           291
% 2.43/0.99  inst_num_of_duplicates:                 0
% 2.43/0.99  inst_inst_num_from_inst_to_res:         0
% 2.43/0.99  inst_dismatching_checking_time:         0.
% 2.43/0.99  
% 2.43/0.99  ------ Resolution
% 2.43/0.99  
% 2.43/0.99  res_num_of_clauses:                     0
% 2.43/0.99  res_num_in_passive:                     0
% 2.43/0.99  res_num_in_active:                      0
% 2.43/0.99  res_num_of_loops:                       100
% 2.43/0.99  res_forward_subset_subsumed:            8
% 2.43/0.99  res_backward_subset_subsumed:           0
% 2.43/0.99  res_forward_subsumed:                   0
% 2.43/0.99  res_backward_subsumed:                  0
% 2.43/0.99  res_forward_subsumption_resolution:     1
% 2.43/0.99  res_backward_subsumption_resolution:    2
% 2.43/0.99  res_clause_to_clause_subsumption:       236
% 2.43/0.99  res_orphan_elimination:                 0
% 2.43/0.99  res_tautology_del:                      8
% 2.43/0.99  res_num_eq_res_simplified:              0
% 2.43/0.99  res_num_sel_changes:                    0
% 2.43/0.99  res_moves_from_active_to_pass:          0
% 2.43/0.99  
% 2.43/0.99  ------ Superposition
% 2.43/0.99  
% 2.43/0.99  sup_time_total:                         0.
% 2.43/0.99  sup_time_generating:                    0.
% 2.43/0.99  sup_time_sim_full:                      0.
% 2.43/0.99  sup_time_sim_immed:                     0.
% 2.43/0.99  
% 2.43/0.99  sup_num_of_clauses:                     37
% 2.43/0.99  sup_num_in_active:                      29
% 2.43/0.99  sup_num_in_passive:                     8
% 2.43/0.99  sup_num_of_loops:                       28
% 2.43/0.99  sup_fw_superposition:                   5
% 2.43/0.99  sup_bw_superposition:                   8
% 2.43/0.99  sup_immediate_simplified:               0
% 2.43/0.99  sup_given_eliminated:                   0
% 2.43/0.99  comparisons_done:                       0
% 2.43/0.99  comparisons_avoided:                    0
% 2.43/0.99  
% 2.43/0.99  ------ Simplifications
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  sim_fw_subset_subsumed:                 0
% 2.43/0.99  sim_bw_subset_subsumed:                 0
% 2.43/0.99  sim_fw_subsumed:                        0
% 2.43/0.99  sim_bw_subsumed:                        0
% 2.43/0.99  sim_fw_subsumption_res:                 2
% 2.43/0.99  sim_bw_subsumption_res:                 0
% 2.43/0.99  sim_tautology_del:                      1
% 2.43/0.99  sim_eq_tautology_del:                   0
% 2.43/0.99  sim_eq_res_simp:                        0
% 2.43/0.99  sim_fw_demodulated:                     5
% 2.43/0.99  sim_bw_demodulated:                     0
% 2.43/0.99  sim_light_normalised:                   9
% 2.43/0.99  sim_joinable_taut:                      0
% 2.43/0.99  sim_joinable_simp:                      0
% 2.43/0.99  sim_ac_normalised:                      0
% 2.43/0.99  sim_smt_subsumption:                    0
% 2.43/0.99  
%------------------------------------------------------------------------------
