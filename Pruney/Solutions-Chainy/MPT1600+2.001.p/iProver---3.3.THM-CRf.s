%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:11 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  212 (1229 expanded)
%              Number of clauses        :  145 ( 501 expanded)
%              Number of leaves         :   19 ( 260 expanded)
%              Depth                    :   30
%              Number of atoms          : 1015 (5406 expanded)
%              Number of equality atoms :  566 (1938 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => ( r2_hidden(k2_xboole_0(X1,X2),X0)
                 => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2)
              & r2_hidden(k2_xboole_0(X1,X2),X0)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2)
              & r2_hidden(k2_xboole_0(X1,X2),X0)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2)
          & r2_hidden(k2_xboole_0(X1,X2),X0)
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( k2_xboole_0(X1,sK4) != k10_lattice3(k2_yellow_1(X0),X1,sK4)
        & r2_hidden(k2_xboole_0(X1,sK4),X0)
        & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2)
              & r2_hidden(k2_xboole_0(X1,X2),X0)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
     => ( ? [X2] :
            ( k2_xboole_0(sK3,X2) != k10_lattice3(k2_yellow_1(X0),sK3,X2)
            & r2_hidden(k2_xboole_0(sK3,X2),X0)
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2)
                & r2_hidden(k2_xboole_0(X1,X2),X0)
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(sK2),X1,X2)
              & r2_hidden(k2_xboole_0(X1,X2),sK2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k2_xboole_0(sK3,sK4) != k10_lattice3(k2_yellow_1(sK2),sK3,sK4)
    & r2_hidden(k2_xboole_0(sK3,sK4),sK2)
    & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f41,f40,f39])).

fof(f72,plain,(
    r2_hidden(k2_xboole_0(sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f62,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f61,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
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
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
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
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ sP0(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP0(X2,X1,X0,X3)
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f25,f30])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP0(X2,X1,X0,X3)
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f33,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ sP0(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_yellow_0(X2,k2_tarski(X1,X0))
        & k10_lattice3(X2,X1,X0) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X2,X3,X4)
          & r1_orders_2(X2,X0,X4)
          & r1_orders_2(X2,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X2,X3,X4)
          & r1_orders_2(X2,X0,X4)
          & r1_orders_2(X2,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,X3,sK1(X0,X1,X2,X3))
        & r1_orders_2(X2,X0,sK1(X0,X1,X2,X3))
        & r1_orders_2(X2,X1,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_yellow_0(X2,k2_tarski(X1,X0))
        & k10_lattice3(X2,X1,X0) = X3 )
      | ( ~ r1_orders_2(X2,X3,sK1(X0,X1,X2,X3))
        & r1_orders_2(X2,X0,sK1(X0,X1,X2,X3))
        & r1_orders_2(X2,X1,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X2,X1,X0) = X3
      | r1_orders_2(X2,X1,sK1(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X2,X1,X0) = X3
      | ~ r1_orders_2(X2,X3,sK1(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X2,X1,X0) = X3
      | r1_orders_2(X2,X0,sK1(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X2,X1,X0) = X3
      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    k2_xboole_0(sK3,sK4) != k10_lattice3(k2_yellow_1(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(k2_xboole_0(sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_783,plain,
    ( r2_hidden(k2_xboole_0(sK3,sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_804,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1590,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_804])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_805,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_806,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_24,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_785,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_858,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_785,c_23])).

cnf(c_5,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_802,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r3_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2815,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top
    | v3_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_802])).

cnf(c_2823,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top
    | v3_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2815,c_23])).

cnf(c_20,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_46,plain,
    ( v3_orders_2(k2_yellow_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_52,plain,
    ( l1_orders_2(k2_yellow_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3364,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2823,c_46,c_52])).

cnf(c_3375,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_3364])).

cnf(c_21,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_43,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v2_struct_0(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4820,plain,
    ( v1_xboole_0(X0) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3375,c_43])).

cnf(c_4821,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4820])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_793,plain,
    ( sP0(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_orders_2(X2,X1,sK1(X0,X1,X2,X3))
    | k10_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_795,plain,
    ( k10_lattice3(X0,X1,X2) = X3
    | sP0(X2,X1,X0,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) != iProver_top
    | r1_orders_2(X0,X1,X3) != iProver_top
    | r1_orders_2(X0,X1,sK1(X2,X1,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X3,sK1(X0,X1,X2,X3))
    | k10_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_797,plain,
    ( k10_lattice3(X0,X1,X2) = X3
    | sP0(X2,X1,X0,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) != iProver_top
    | r1_orders_2(X0,X1,X3) != iProver_top
    | r1_orders_2(X0,X3,sK1(X2,X1,X0,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2221,plain,
    ( k10_lattice3(X0,X1,X2) = X1
    | sP0(X2,X1,X0,X1) != iProver_top
    | r1_orders_2(X0,X2,X1) != iProver_top
    | r1_orders_2(X0,X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_797])).

cnf(c_4352,plain,
    ( k10_lattice3(X0,X1,X2) = X1
    | r1_orders_2(X0,X2,X1) != iProver_top
    | r1_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_2221])).

cnf(c_4886,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X1
    | r1_orders_2(k2_yellow_1(X0),X1,X1) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v5_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4821,c_4352])).

cnf(c_4923,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X1
    | r1_orders_2(k2_yellow_1(X0),X1,X1) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v5_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4886,c_23])).

cnf(c_19,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_49,plain,
    ( v5_orders_2(k2_yellow_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5279,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X1
    | r1_orders_2(k2_yellow_1(X0),X1,X1) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4923,c_49,c_52])).

cnf(c_5291,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X1
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X1,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4821,c_5279])).

cnf(c_19613,plain,
    ( k10_lattice3(k2_yellow_1(X0),k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_5291])).

cnf(c_20049,plain,
    ( k10_lattice3(k2_yellow_1(X0),k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | r1_tarski(X2,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(X1,k2_xboole_0(X1,X2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_19613])).

cnf(c_1478,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_806])).

cnf(c_20865,plain,
    ( k10_lattice3(k2_yellow_1(X0),k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20049,c_806,c_1478])).

cnf(c_20870,plain,
    ( k10_lattice3(k2_yellow_1(X0),k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X2,X1),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_20865])).

cnf(c_20987,plain,
    ( k10_lattice3(k2_yellow_1(sK2),k2_xboole_0(sK4,sK3),sK4) = k2_xboole_0(sK4,sK3)
    | m1_subset_1(sK4,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1590,c_20870])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_782,plain,
    ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_822,plain,
    ( m1_subset_1(sK4,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_782,c_23])).

cnf(c_20998,plain,
    ( k10_lattice3(k2_yellow_1(sK2),k2_xboole_0(sK4,sK3),sK4) = k2_xboole_0(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20987,c_31,c_822])).

cnf(c_21001,plain,
    ( k10_lattice3(k2_yellow_1(sK2),k2_xboole_0(sK3,sK4),sK4) = k2_xboole_0(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_20998])).

cnf(c_16,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_791,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) = iProver_top
    | r1_yellow_0(X0,k2_tarski(X2,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1913,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X2,X1)) = iProver_top
    | r1_yellow_0(k2_yellow_1(X0),k2_tarski(X2,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X2,X1),X0) != iProver_top
    | v5_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_791])).

cnf(c_1914,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X2,X1)) = iProver_top
    | r1_yellow_0(k2_yellow_1(X0),k2_tarski(X2,X1)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X2,X1),X0) != iProver_top
    | v5_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1913,c_23])).

cnf(c_3995,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X2,X1)) = iProver_top
    | r1_yellow_0(k2_yellow_1(X0),k2_tarski(X2,X1)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X2,X1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1914,c_49,c_52])).

cnf(c_21542,plain,
    ( r1_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
    | r1_yellow_0(k2_yellow_1(sK2),k2_tarski(k2_xboole_0(sK3,sK4),sK4)) != iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(sK2),k2_xboole_0(sK3,sK4),sK4),sK2) != iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_21001,c_3995])).

cnf(c_21758,plain,
    ( r1_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
    | r1_yellow_0(k2_yellow_1(sK2),k2_tarski(k2_xboole_0(sK3,sK4),sK4)) != iProver_top
    | m1_subset_1(k2_xboole_0(sK4,sK3),sK2) != iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21542,c_21001])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_34,plain,
    ( r2_hidden(k2_xboole_0(sK3,sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_41,plain,
    ( u1_struct_0(k2_yellow_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_45,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v2_struct_0(k2_yellow_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_48,plain,
    ( v3_orders_2(k2_yellow_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_54,plain,
    ( l1_orders_2(k2_yellow_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_1131,plain,
    ( ~ r2_hidden(k2_xboole_0(sK3,sK4),sK2)
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1132,plain,
    ( r2_hidden(k2_xboole_0(sK3,sK4),sK2) != iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_1314,plain,
    ( k2_xboole_0(sK4,sK3) = k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1203,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k2_xboole_0(X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,k2_xboole_0(X1,X2))
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1894,plain,
    ( r3_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(sK4,k2_xboole_0(sK4,sK3))
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_1899,plain,
    ( r3_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
    | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(sK4,k2_xboole_0(sK4,sK3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1901,plain,
    ( r3_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
    | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | r1_tarski(sK4,k2_xboole_0(sK4,sK3)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1258,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
    | X0 != k2_xboole_0(sK3,sK4)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_1543,plain,
    ( m1_subset_1(k2_xboole_0(sK4,sK3),X0)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
    | X0 != sK2
    | k2_xboole_0(sK4,sK3) != k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_2002,plain,
    ( m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
    | k2_xboole_0(sK4,sK3) != k2_xboole_0(sK3,sK4)
    | u1_struct_0(k2_yellow_1(X0)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_2004,plain,
    ( k2_xboole_0(sK4,sK3) != k2_xboole_0(sK3,sK4)
    | u1_struct_0(k2_yellow_1(X0)) != sK2
    | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0))) = iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2002])).

cnf(c_2006,plain,
    ( k2_xboole_0(sK4,sK3) != k2_xboole_0(sK3,sK4)
    | u1_struct_0(k2_yellow_1(sK2)) != sK2
    | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(sK2))) = iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_3336,plain,
    ( r1_tarski(sK4,k2_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3337,plain,
    ( r1_tarski(sK4,k2_xboole_0(sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3336])).

cnf(c_16667,plain,
    ( r1_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3))
    | ~ r3_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ v3_orders_2(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_16673,plain,
    ( r1_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
    | r3_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3)) != iProver_top
    | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top
    | v3_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16667])).

cnf(c_16675,plain,
    ( r1_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
    | r3_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) != iProver_top
    | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | v2_struct_0(k2_yellow_1(sK2)) = iProver_top
    | v3_orders_2(k2_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k2_yellow_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16673])).

cnf(c_22010,plain,
    ( r1_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21758,c_31,c_33,c_34,c_41,c_45,c_48,c_54,c_1132,c_1314,c_1901,c_2006,c_3337,c_16675])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_orders_2(X2,X0,sK1(X0,X1,X2,X3))
    | k10_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_796,plain,
    ( k10_lattice3(X0,X1,X2) = X3
    | sP0(X2,X1,X0,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) != iProver_top
    | r1_orders_2(X0,X1,X3) != iProver_top
    | r1_orders_2(X0,X2,sK1(X2,X1,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2))
    | k10_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_794,plain,
    ( k10_lattice3(X0,X1,X2) = X3
    | sP0(X2,X1,X0,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) != iProver_top
    | r1_orders_2(X0,X1,X3) != iProver_top
    | m1_subset_1(sK1(X2,X1,X0,X3),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1824,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(sK1(X2,X1,k2_yellow_1(X0),X3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_794])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_803,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r3_orders_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3028,plain,
    ( k10_lattice3(k2_yellow_1(u1_struct_0(X0)),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(u1_struct_0(X0)),X3) != iProver_top
    | r1_orders_2(X0,X4,sK1(X2,X1,k2_yellow_1(u1_struct_0(X0)),X3)) != iProver_top
    | r1_orders_2(k2_yellow_1(u1_struct_0(X0)),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(u1_struct_0(X0)),X1,X3) != iProver_top
    | r3_orders_2(X0,X4,sK1(X2,X1,k2_yellow_1(u1_struct_0(X0)),X3)) = iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_803])).

cnf(c_10531,plain,
    ( k10_lattice3(k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
    | r1_orders_2(k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X1,X3) != iProver_top
    | r3_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X3)) = iProver_top
    | m1_subset_1(X4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top
    | v3_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_3028])).

cnf(c_10542,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
    | r3_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top
    | v3_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10531,c_23])).

cnf(c_10625,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
    | r3_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10542,c_46,c_52])).

cnf(c_10642,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | r3_orders_2(k2_yellow_1(X0),X2,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_10625])).

cnf(c_25,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_784,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_847,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_784,c_23])).

cnf(c_10849,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK1(X2,X1,k2_yellow_1(X0),X3),X0) != iProver_top
    | r1_tarski(X2,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10642,c_847])).

cnf(c_12233,plain,
    ( v1_xboole_0(X0) = iProver_top
    | r1_tarski(X2,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10849,c_43,c_1824])).

cnf(c_12234,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X2,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_12233])).

cnf(c_10641,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | r3_orders_2(k2_yellow_1(X0),X1,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_10625])).

cnf(c_10777,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(sK1(X2,X1,k2_yellow_1(X0),X3),X0) != iProver_top
    | r1_tarski(X1,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10641,c_847])).

cnf(c_12204,plain,
    ( v1_xboole_0(X0) = iProver_top
    | r1_tarski(X1,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10777,c_43,c_1824])).

cnf(c_12205,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_12204])).

cnf(c_4832,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(sK1(X2,X1,k2_yellow_1(X0),X3),X0) != iProver_top
    | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4821,c_797])).

cnf(c_11901,plain,
    ( m1_subset_1(X3,X0) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4832,c_1824])).

cnf(c_11902,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
    | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11901])).

cnf(c_11914,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X3,X4)
    | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X3,X4)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X3,X4)) != iProver_top
    | m1_subset_1(k2_xboole_0(X3,X4),X0) != iProver_top
    | r1_tarski(X4,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4))) != iProver_top
    | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_11902])).

cnf(c_18155,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X3,X4)
    | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X3,X4)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X3,X4)) != iProver_top
    | m1_subset_1(k2_xboole_0(X3,X4),X0) != iProver_top
    | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4))) != iProver_top
    | r1_tarski(X4,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X4,X3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_11914])).

cnf(c_18304,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X3)
    | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X1,X3)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X3)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X3)) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X3),X0) != iProver_top
    | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12205,c_18155])).

cnf(c_19128,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X3)
    | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X1,X3)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X3)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X3)) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X3),X0) != iProver_top
    | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X1,X3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_18304])).

cnf(c_19380,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X1,X2)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12234,c_19128])).

cnf(c_19432,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X2,X1)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_19380])).

cnf(c_19431,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v5_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_19380])).

cnf(c_19462,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v5_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19431,c_23])).

cnf(c_19756,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19432,c_49,c_52,c_19462])).

cnf(c_19771,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X2,X1)) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_19756])).

cnf(c_22020,plain,
    ( k10_lattice3(k2_yellow_1(sK2),sK3,sK4) = k2_xboole_0(sK3,sK4)
    | r1_orders_2(k2_yellow_1(sK2),sK3,k2_xboole_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,sK2) != iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_22010,c_19771])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_781,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_819,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_781,c_23])).

cnf(c_258,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1326,plain,
    ( k2_xboole_0(sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_1988,plain,
    ( r3_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(sK3,k2_xboole_0(sK3,sK4))
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_1993,plain,
    ( r3_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4)) = iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1988])).

cnf(c_1995,plain,
    ( r3_orders_2(k2_yellow_1(sK2),sK3,k2_xboole_0(sK3,sK4)) = iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_1553,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),X0)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
    | X0 != sK2
    | k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_2019,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
    | k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4)
    | u1_struct_0(k2_yellow_1(X0)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_2021,plain,
    ( k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4)
    | u1_struct_0(k2_yellow_1(X0)) != sK2
    | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0))) = iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2019])).

cnf(c_2023,plain,
    ( k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4)
    | u1_struct_0(k2_yellow_1(sK2)) != sK2
    | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) = iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2021])).

cnf(c_3342,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3343,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3342])).

cnf(c_16678,plain,
    ( r1_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4))
    | ~ r3_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ v3_orders_2(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_16684,plain,
    ( r1_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4)) = iProver_top
    | r3_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top
    | v3_orders_2(k2_yellow_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16678])).

cnf(c_16686,plain,
    ( r1_orders_2(k2_yellow_1(sK2),sK3,k2_xboole_0(sK3,sK4)) = iProver_top
    | r3_orders_2(k2_yellow_1(sK2),sK3,k2_xboole_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | v2_struct_0(k2_yellow_1(sK2)) = iProver_top
    | v3_orders_2(k2_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k2_yellow_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16684])).

cnf(c_31845,plain,
    ( k10_lattice3(k2_yellow_1(sK2),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22020,c_31,c_32,c_34,c_41,c_45,c_48,c_54,c_822,c_819,c_1132,c_1326,c_1995,c_2023,c_3343,c_16686])).

cnf(c_26,negated_conjecture,
    ( k2_xboole_0(sK3,sK4) != k10_lattice3(k2_yellow_1(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_31848,plain,
    ( k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_31845,c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31848,c_1326])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:08:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 7.81/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.49  
% 7.81/1.49  ------  iProver source info
% 7.81/1.49  
% 7.81/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.49  git: non_committed_changes: false
% 7.81/1.49  git: last_make_outside_of_git: false
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    --mode clausify
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             sel
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         604.99
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              none
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           false
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             false
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         false
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     num_symb
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       true
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     false
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   []
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_full_bw                           [BwDemod]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  ------ Parsing...
% 7.81/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.49  ------ Proving...
% 7.81/1.49  ------ Problem Properties 
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  clauses                                 31
% 7.81/1.49  conjectures                             5
% 7.81/1.49  EPR                                     2
% 7.81/1.49  Horn                                    21
% 7.81/1.49  unary                                   12
% 7.81/1.49  binary                                  2
% 7.81/1.49  lits                                    113
% 7.81/1.49  lits eq                                 8
% 7.81/1.49  fd_pure                                 0
% 7.81/1.49  fd_pseudo                               0
% 7.81/1.49  fd_cond                                 0
% 7.81/1.49  fd_pseudo_cond                          4
% 7.81/1.49  AC symbols                              0
% 7.81/1.49  
% 7.81/1.49  ------ Input Options Time Limit: Unbounded
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  Current options:
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    --mode clausify
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             sel
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         604.99
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              none
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           false
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             false
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         false
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     num_symb
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       true
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     false
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   []
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_full_bw                           [BwDemod]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ Proving...
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  % SZS status Theorem for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  fof(f1,axiom,(
% 7.81/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f43,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f1])).
% 7.81/1.49  
% 7.81/1.49  fof(f12,conjecture,(
% 7.81/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f13,negated_conjecture,(
% 7.81/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 7.81/1.49    inference(negated_conjecture,[],[f12])).
% 7.81/1.49  
% 7.81/1.49  fof(f28,plain,(
% 7.81/1.49    ? [X0] : (? [X1] : (? [X2] : ((k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),X0)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 7.81/1.49    inference(ennf_transformation,[],[f13])).
% 7.81/1.49  
% 7.81/1.49  fof(f29,plain,(
% 7.81/1.49    ? [X0] : (? [X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),X0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 7.81/1.49    inference(flattening,[],[f28])).
% 7.81/1.49  
% 7.81/1.49  fof(f41,plain,(
% 7.81/1.49    ( ! [X0,X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),X0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (k2_xboole_0(X1,sK4) != k10_lattice3(k2_yellow_1(X0),X1,sK4) & r2_hidden(k2_xboole_0(X1,sK4),X0) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))))) )),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f40,plain,(
% 7.81/1.49    ( ! [X0] : (? [X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),X0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (k2_xboole_0(sK3,X2) != k10_lattice3(k2_yellow_1(X0),sK3,X2) & r2_hidden(k2_xboole_0(sK3,X2),X0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f39,plain,(
% 7.81/1.49    ? [X0] : (? [X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),X0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(sK2),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),sK2) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))) & ~v1_xboole_0(sK2))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f42,plain,(
% 7.81/1.49    ((k2_xboole_0(sK3,sK4) != k10_lattice3(k2_yellow_1(sK2),sK3,sK4) & r2_hidden(k2_xboole_0(sK3,sK4),sK2) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))) & ~v1_xboole_0(sK2)),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f41,f40,f39])).
% 7.81/1.49  
% 7.81/1.49  fof(f72,plain,(
% 7.81/1.49    r2_hidden(k2_xboole_0(sK3,sK4),sK2)),
% 7.81/1.49    inference(cnf_transformation,[],[f42])).
% 7.81/1.49  
% 7.81/1.49  fof(f4,axiom,(
% 7.81/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f21,plain,(
% 7.81/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.81/1.49    inference(ennf_transformation,[],[f4])).
% 7.81/1.49  
% 7.81/1.49  fof(f46,plain,(
% 7.81/1.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f21])).
% 7.81/1.49  
% 7.81/1.49  fof(f3,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f19,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.81/1.49    inference(ennf_transformation,[],[f3])).
% 7.81/1.49  
% 7.81/1.49  fof(f20,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.81/1.49    inference(flattening,[],[f19])).
% 7.81/1.49  
% 7.81/1.49  fof(f45,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f20])).
% 7.81/1.49  
% 7.81/1.49  fof(f2,axiom,(
% 7.81/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f44,plain,(
% 7.81/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f2])).
% 7.81/1.49  
% 7.81/1.49  fof(f11,axiom,(
% 7.81/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f27,plain,(
% 7.81/1.49    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 7.81/1.49    inference(ennf_transformation,[],[f11])).
% 7.81/1.49  
% 7.81/1.49  fof(f38,plain,(
% 7.81/1.49    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 7.81/1.49    inference(nnf_transformation,[],[f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f68,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f38])).
% 7.81/1.49  
% 7.81/1.49  fof(f10,axiom,(
% 7.81/1.49    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f65,plain,(
% 7.81/1.49    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 7.81/1.49    inference(cnf_transformation,[],[f10])).
% 7.81/1.49  
% 7.81/1.49  fof(f5,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f22,plain,(
% 7.81/1.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.81/1.49    inference(ennf_transformation,[],[f5])).
% 7.81/1.49  
% 7.81/1.49  fof(f23,plain,(
% 7.81/1.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.81/1.49    inference(flattening,[],[f22])).
% 7.81/1.49  
% 7.81/1.49  fof(f32,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.81/1.49    inference(nnf_transformation,[],[f23])).
% 7.81/1.49  
% 7.81/1.49  fof(f47,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f32])).
% 7.81/1.49  
% 7.81/1.49  fof(f8,axiom,(
% 7.81/1.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f15,plain,(
% 7.81/1.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 7.81/1.49    inference(pure_predicate_removal,[],[f8])).
% 7.81/1.49  
% 7.81/1.49  fof(f17,plain,(
% 7.81/1.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 7.81/1.49    inference(pure_predicate_removal,[],[f15])).
% 7.81/1.49  
% 7.81/1.49  fof(f62,plain,(
% 7.81/1.49    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f17])).
% 7.81/1.49  
% 7.81/1.49  fof(f7,axiom,(
% 7.81/1.49    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f16,plain,(
% 7.81/1.49    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 7.81/1.49    inference(pure_predicate_removal,[],[f7])).
% 7.81/1.49  
% 7.81/1.49  fof(f61,plain,(
% 7.81/1.49    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f16])).
% 7.81/1.49  
% 7.81/1.49  fof(f9,axiom,(
% 7.81/1.49    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f18,plain,(
% 7.81/1.49    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 7.81/1.49    inference(pure_predicate_removal,[],[f9])).
% 7.81/1.49  
% 7.81/1.49  fof(f26,plain,(
% 7.81/1.49    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 7.81/1.49    inference(ennf_transformation,[],[f18])).
% 7.81/1.49  
% 7.81/1.49  fof(f64,plain,(
% 7.81/1.49    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f26])).
% 7.81/1.49  
% 7.81/1.49  fof(f6,axiom,(
% 7.81/1.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) => (r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3)) & ((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))))))))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f14,plain,(
% 7.81/1.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) => (r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3)) & ((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X5) & r1_orders_2(X0,X1,X5)) => r1_orders_2(X0,X3,X5))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))))))))),
% 7.81/1.49    inference(rectify,[],[f6])).
% 7.81/1.49  
% 7.81/1.49  fof(f24,plain,(
% 7.81/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) | (? [X4] : ((~r1_orders_2(X0,X3,X4) & (r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4))) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X5] : ((r1_orders_2(X0,X3,X5) | (~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5))) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | (~r1_yellow_0(X0,k2_tarski(X1,X2)) | k10_lattice3(X0,X1,X2) != X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 7.81/1.49    inference(ennf_transformation,[],[f14])).
% 7.81/1.49  
% 7.81/1.49  fof(f25,plain,(
% 7.81/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 7.81/1.49    inference(flattening,[],[f24])).
% 7.81/1.49  
% 7.81/1.49  fof(f30,plain,(
% 7.81/1.49    ! [X2,X1,X0,X3] : ((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~sP0(X2,X1,X0,X3))),
% 7.81/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.81/1.49  
% 7.81/1.49  fof(f31,plain,(
% 7.81/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((sP0(X2,X1,X0,X3) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 7.81/1.49    inference(definition_folding,[],[f25,f30])).
% 7.81/1.49  
% 7.81/1.49  fof(f37,plain,(
% 7.81/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((sP0(X2,X1,X0,X3) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 7.81/1.49    inference(rectify,[],[f31])).
% 7.81/1.49  
% 7.81/1.49  fof(f60,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f37])).
% 7.81/1.49  
% 7.81/1.49  fof(f33,plain,(
% 7.81/1.49    ! [X2,X1,X0,X3] : ((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~sP0(X2,X1,X0,X3))),
% 7.81/1.49    inference(nnf_transformation,[],[f30])).
% 7.81/1.49  
% 7.81/1.49  fof(f34,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((r1_yellow_0(X2,k2_tarski(X1,X0)) & k10_lattice3(X2,X1,X0) = X3) | ? [X4] : (~r1_orders_2(X2,X3,X4) & r1_orders_2(X2,X0,X4) & r1_orders_2(X2,X1,X4) & m1_subset_1(X4,u1_struct_0(X2))) | ~r1_orders_2(X2,X0,X3) | ~r1_orders_2(X2,X1,X3) | ~sP0(X0,X1,X2,X3))),
% 7.81/1.49    inference(rectify,[],[f33])).
% 7.81/1.49  
% 7.81/1.49  fof(f35,plain,(
% 7.81/1.49    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X2,X3,X4) & r1_orders_2(X2,X0,X4) & r1_orders_2(X2,X1,X4) & m1_subset_1(X4,u1_struct_0(X2))) => (~r1_orders_2(X2,X3,sK1(X0,X1,X2,X3)) & r1_orders_2(X2,X0,sK1(X0,X1,X2,X3)) & r1_orders_2(X2,X1,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2))))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f36,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((r1_yellow_0(X2,k2_tarski(X1,X0)) & k10_lattice3(X2,X1,X0) = X3) | (~r1_orders_2(X2,X3,sK1(X0,X1,X2,X3)) & r1_orders_2(X2,X0,sK1(X0,X1,X2,X3)) & r1_orders_2(X2,X1,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2))) | ~r1_orders_2(X2,X0,X3) | ~r1_orders_2(X2,X1,X3) | ~sP0(X0,X1,X2,X3))),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 7.81/1.49  
% 7.81/1.49  fof(f50,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (k10_lattice3(X2,X1,X0) = X3 | r1_orders_2(X2,X1,sK1(X0,X1,X2,X3)) | ~r1_orders_2(X2,X0,X3) | ~r1_orders_2(X2,X1,X3) | ~sP0(X0,X1,X2,X3)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f36])).
% 7.81/1.49  
% 7.81/1.49  fof(f52,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (k10_lattice3(X2,X1,X0) = X3 | ~r1_orders_2(X2,X3,sK1(X0,X1,X2,X3)) | ~r1_orders_2(X2,X0,X3) | ~r1_orders_2(X2,X1,X3) | ~sP0(X0,X1,X2,X3)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f36])).
% 7.81/1.49  
% 7.81/1.49  fof(f63,plain,(
% 7.81/1.49    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f17])).
% 7.81/1.49  
% 7.81/1.49  fof(f69,plain,(
% 7.81/1.49    ~v1_xboole_0(sK2)),
% 7.81/1.49    inference(cnf_transformation,[],[f42])).
% 7.81/1.49  
% 7.81/1.49  fof(f71,plain,(
% 7.81/1.49    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))),
% 7.81/1.49    inference(cnf_transformation,[],[f42])).
% 7.81/1.49  
% 7.81/1.49  fof(f58,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f37])).
% 7.81/1.49  
% 7.81/1.49  fof(f75,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 7.81/1.49    inference(equality_resolution,[],[f58])).
% 7.81/1.49  
% 7.81/1.49  fof(f51,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (k10_lattice3(X2,X1,X0) = X3 | r1_orders_2(X2,X0,sK1(X0,X1,X2,X3)) | ~r1_orders_2(X2,X0,X3) | ~r1_orders_2(X2,X1,X3) | ~sP0(X0,X1,X2,X3)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f36])).
% 7.81/1.49  
% 7.81/1.49  fof(f49,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (k10_lattice3(X2,X1,X0) = X3 | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2)) | ~r1_orders_2(X2,X0,X3) | ~r1_orders_2(X2,X1,X3) | ~sP0(X0,X1,X2,X3)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f36])).
% 7.81/1.49  
% 7.81/1.49  fof(f48,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f32])).
% 7.81/1.49  
% 7.81/1.49  fof(f67,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f38])).
% 7.81/1.49  
% 7.81/1.49  fof(f70,plain,(
% 7.81/1.49    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))),
% 7.81/1.49    inference(cnf_transformation,[],[f42])).
% 7.81/1.49  
% 7.81/1.49  fof(f73,plain,(
% 7.81/1.49    k2_xboole_0(sK3,sK4) != k10_lattice3(k2_yellow_1(sK2),sK3,sK4)),
% 7.81/1.49    inference(cnf_transformation,[],[f42])).
% 7.81/1.49  
% 7.81/1.49  cnf(c_0,plain,
% 7.81/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_27,negated_conjecture,
% 7.81/1.49      ( r2_hidden(k2_xboole_0(sK3,sK4),sK2) ),
% 7.81/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_783,plain,
% 7.81/1.49      ( r2_hidden(k2_xboole_0(sK3,sK4),sK2) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3,plain,
% 7.81/1.49      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_804,plain,
% 7.81/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.81/1.49      | m1_subset_1(X0,X1) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1590,plain,
% 7.81/1.49      ( m1_subset_1(k2_xboole_0(sK3,sK4),sK2) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_783,c_804]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2,plain,
% 7.81/1.49      ( ~ r1_tarski(X0,X1)
% 7.81/1.49      | ~ r1_tarski(X2,X1)
% 7.81/1.49      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_805,plain,
% 7.81/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.81/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.81/1.49      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1,plain,
% 7.81/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_806,plain,
% 7.81/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_24,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 7.81/1.49      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ r1_tarski(X1,X2)
% 7.81/1.49      | v1_xboole_0(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_785,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 7.81/1.49      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23,plain,
% 7.81/1.49      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 7.81/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_858,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_785,c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5,plain,
% 7.81/1.49      ( r1_orders_2(X0,X1,X2)
% 7.81/1.49      | ~ r3_orders_2(X0,X1,X2)
% 7.81/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.81/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.81/1.49      | v2_struct_0(X0)
% 7.81/1.49      | ~ v3_orders_2(X0)
% 7.81/1.49      | ~ l1_orders_2(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_802,plain,
% 7.81/1.49      ( r1_orders_2(X0,X1,X2) = iProver_top
% 7.81/1.49      | r3_orders_2(X0,X1,X2) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | v2_struct_0(X0) = iProver_top
% 7.81/1.49      | v3_orders_2(X0) != iProver_top
% 7.81/1.49      | l1_orders_2(X0) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2815,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top
% 7.81/1.49      | v3_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_23,c_802]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2823,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top
% 7.81/1.49      | v3_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_2815,c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20,plain,
% 7.81/1.49      ( v3_orders_2(k2_yellow_1(X0)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_46,plain,
% 7.81/1.49      ( v3_orders_2(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_18,plain,
% 7.81/1.49      ( l1_orders_2(k2_yellow_1(X0)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_52,plain,
% 7.81/1.49      ( l1_orders_2(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3364,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_2823,c_46,c_52]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3375,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_858,c_3364]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_21,plain,
% 7.81/1.49      ( v1_xboole_0(X0) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_43,plain,
% 7.81/1.49      ( v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4820,plain,
% 7.81/1.49      ( v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_3375,c_43]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4821,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(renaming,[status(thm)],[c_4820]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_14,plain,
% 7.81/1.49      ( sP0(X0,X1,X2,X3)
% 7.81/1.49      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 7.81/1.49      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 7.81/1.49      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 7.81/1.49      | ~ v5_orders_2(X2)
% 7.81/1.49      | ~ l1_orders_2(X2) ),
% 7.81/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_793,plain,
% 7.81/1.49      ( sP0(X0,X1,X2,X3) = iProver_top
% 7.81/1.49      | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(X2)) != iProver_top
% 7.81/1.49      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 7.81/1.49      | v5_orders_2(X2) != iProver_top
% 7.81/1.49      | l1_orders_2(X2) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_12,plain,
% 7.81/1.49      ( ~ sP0(X0,X1,X2,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X0,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X1,X3)
% 7.81/1.49      | r1_orders_2(X2,X1,sK1(X0,X1,X2,X3))
% 7.81/1.49      | k10_lattice3(X2,X1,X0) = X3 ),
% 7.81/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_795,plain,
% 7.81/1.49      ( k10_lattice3(X0,X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,X0,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X1,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X1,sK1(X2,X1,X0,X3)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10,plain,
% 7.81/1.49      ( ~ sP0(X0,X1,X2,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X0,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X1,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X3,sK1(X0,X1,X2,X3))
% 7.81/1.49      | k10_lattice3(X2,X1,X0) = X3 ),
% 7.81/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_797,plain,
% 7.81/1.49      ( k10_lattice3(X0,X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,X0,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X1,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X3,sK1(X2,X1,X0,X3)) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2221,plain,
% 7.81/1.49      ( k10_lattice3(X0,X1,X2) = X1
% 7.81/1.49      | sP0(X2,X1,X0,X1) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X2,X1) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X1,X1) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_795,c_797]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4352,plain,
% 7.81/1.49      ( k10_lattice3(X0,X1,X2) = X1
% 7.81/1.49      | r1_orders_2(X0,X2,X1) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X1,X1) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | v5_orders_2(X0) != iProver_top
% 7.81/1.49      | l1_orders_2(X0) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_793,c_2221]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4886,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X1
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X1) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | v5_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_4821,c_4352]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4923,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X1
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X1) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | v5_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_4886,c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19,plain,
% 7.81/1.49      ( v5_orders_2(k2_yellow_1(X0)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_49,plain,
% 7.81/1.49      ( v5_orders_2(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5279,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X1
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X1) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_4923,c_49,c_52]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5291,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X1
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.81/1.49      | r1_tarski(X1,X1) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_4821,c_5279]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19613,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.49      | r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_806,c_5291]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20049,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.49      | r1_tarski(X2,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.49      | r1_tarski(X1,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_805,c_19613]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1478,plain,
% 7.81/1.49      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_806]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20865,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(forward_subsumption_resolution,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_20049,c_806,c_1478]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20870,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(X2,X1),X0) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_20865]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20987,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(sK2),k2_xboole_0(sK4,sK3),sK4) = k2_xboole_0(sK4,sK3)
% 7.81/1.49      | m1_subset_1(sK4,sK2) != iProver_top
% 7.81/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1590,c_20870]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_30,negated_conjecture,
% 7.81/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.81/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_31,plain,
% 7.81/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_28,negated_conjecture,
% 7.81/1.49      ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_782,plain,
% 7.81/1.49      ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_822,plain,
% 7.81/1.49      ( m1_subset_1(sK4,sK2) = iProver_top ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_782,c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_20998,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(sK2),k2_xboole_0(sK4,sK3),sK4) = k2_xboole_0(sK4,sK3) ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_20987,c_31,c_822]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_21001,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(sK2),k2_xboole_0(sK3,sK4),sK4) = k2_xboole_0(sK4,sK3) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_20998]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_16,plain,
% 7.81/1.49      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 7.81/1.49      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
% 7.81/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.81/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.81/1.49      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 7.81/1.49      | ~ v5_orders_2(X0)
% 7.81/1.49      | ~ l1_orders_2(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_791,plain,
% 7.81/1.49      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) = iProver_top
% 7.81/1.49      | r1_yellow_0(X0,k2_tarski(X2,X1)) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | v5_orders_2(X0) != iProver_top
% 7.81/1.49      | l1_orders_2(X0) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1913,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X2,X1)) = iProver_top
% 7.81/1.49      | r1_yellow_0(k2_yellow_1(X0),k2_tarski(X2,X1)) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X2,X1),X0) != iProver_top
% 7.81/1.49      | v5_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_23,c_791]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1914,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X2,X1)) = iProver_top
% 7.81/1.49      | r1_yellow_0(k2_yellow_1(X0),k2_tarski(X2,X1)) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X2,X1),X0) != iProver_top
% 7.81/1.49      | v5_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_1913,c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3995,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X2,X1)) = iProver_top
% 7.81/1.49      | r1_yellow_0(k2_yellow_1(X0),k2_tarski(X2,X1)) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X2,X1),X0) != iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_1914,c_49,c_52]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_21542,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
% 7.81/1.49      | r1_yellow_0(k2_yellow_1(sK2),k2_tarski(k2_xboole_0(sK3,sK4),sK4)) != iProver_top
% 7.81/1.49      | m1_subset_1(k10_lattice3(k2_yellow_1(sK2),k2_xboole_0(sK3,sK4),sK4),sK2) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,sK2) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_21001,c_3995]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_21758,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
% 7.81/1.49      | r1_yellow_0(k2_yellow_1(sK2),k2_tarski(k2_xboole_0(sK3,sK4),sK4)) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK4,sK3),sK2) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,sK2) != iProver_top ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_21542,c_21001]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_33,plain,
% 7.81/1.49      ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_34,plain,
% 7.81/1.49      ( r2_hidden(k2_xboole_0(sK3,sK4),sK2) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_41,plain,
% 7.81/1.49      ( u1_struct_0(k2_yellow_1(sK2)) = sK2 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_45,plain,
% 7.81/1.49      ( v1_xboole_0(sK2) = iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(sK2)) != iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_43]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_48,plain,
% 7.81/1.49      ( v3_orders_2(k2_yellow_1(sK2)) = iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_46]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_54,plain,
% 7.81/1.49      ( l1_orders_2(k2_yellow_1(sK2)) = iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_52]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1131,plain,
% 7.81/1.49      ( ~ r2_hidden(k2_xboole_0(sK3,sK4),sK2)
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1132,plain,
% 7.81/1.49      ( r2_hidden(k2_xboole_0(sK3,sK4),sK2) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1131]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1314,plain,
% 7.81/1.49      ( k2_xboole_0(sK4,sK3) = k2_xboole_0(sK3,sK4) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1203,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2))
% 7.81/1.49      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ m1_subset_1(k2_xboole_0(X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ r1_tarski(X1,k2_xboole_0(X1,X2))
% 7.81/1.49      | v1_xboole_0(X0) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1894,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3))
% 7.81/1.49      | ~ m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ r1_tarski(sK4,k2_xboole_0(sK4,sK3))
% 7.81/1.49      | v1_xboole_0(X0) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1203]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1899,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | r1_tarski(sK4,k2_xboole_0(sK4,sK3)) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1901,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 7.81/1.49      | r1_tarski(sK4,k2_xboole_0(sK4,sK3)) != iProver_top
% 7.81/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1899]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_262,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.81/1.49      theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1258,plain,
% 7.81/1.49      ( m1_subset_1(X0,X1)
% 7.81/1.49      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
% 7.81/1.49      | X0 != k2_xboole_0(sK3,sK4)
% 7.81/1.49      | X1 != sK2 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_262]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1543,plain,
% 7.81/1.49      ( m1_subset_1(k2_xboole_0(sK4,sK3),X0)
% 7.81/1.49      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
% 7.81/1.49      | X0 != sK2
% 7.81/1.49      | k2_xboole_0(sK4,sK3) != k2_xboole_0(sK3,sK4) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1258]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2002,plain,
% 7.81/1.49      ( m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
% 7.81/1.49      | k2_xboole_0(sK4,sK3) != k2_xboole_0(sK3,sK4)
% 7.81/1.49      | u1_struct_0(k2_yellow_1(X0)) != sK2 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1543]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2004,plain,
% 7.81/1.49      ( k2_xboole_0(sK4,sK3) != k2_xboole_0(sK3,sK4)
% 7.81/1.49      | u1_struct_0(k2_yellow_1(X0)) != sK2
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0))) = iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_2002]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2006,plain,
% 7.81/1.49      ( k2_xboole_0(sK4,sK3) != k2_xboole_0(sK3,sK4)
% 7.81/1.49      | u1_struct_0(k2_yellow_1(sK2)) != sK2
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(sK2))) = iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_2004]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3336,plain,
% 7.81/1.49      ( r1_tarski(sK4,k2_xboole_0(sK4,sK3)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3337,plain,
% 7.81/1.49      ( r1_tarski(sK4,k2_xboole_0(sK4,sK3)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_3336]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_16667,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3))
% 7.81/1.49      | ~ r3_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3))
% 7.81/1.49      | ~ m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0))
% 7.81/1.49      | ~ v3_orders_2(k2_yellow_1(X0))
% 7.81/1.49      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_16673,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),sK4,k2_xboole_0(sK4,sK3)) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top
% 7.81/1.49      | v3_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_16667]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_16675,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) != iProver_top
% 7.81/1.49      | m1_subset_1(k2_xboole_0(sK4,sK3),u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(sK2)) = iProver_top
% 7.81/1.49      | v3_orders_2(k2_yellow_1(sK2)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(sK2)) != iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_16673]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_22010,plain,
% 7.81/1.49      ( r1_orders_2(k2_yellow_1(sK2),sK4,k2_xboole_0(sK4,sK3)) = iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_21758,c_31,c_33,c_34,c_41,c_45,c_48,c_54,c_1132,
% 7.81/1.49                 c_1314,c_1901,c_2006,c_3337,c_16675]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_11,plain,
% 7.81/1.49      ( ~ sP0(X0,X1,X2,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X0,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X1,X3)
% 7.81/1.49      | r1_orders_2(X2,X0,sK1(X0,X1,X2,X3))
% 7.81/1.49      | k10_lattice3(X2,X1,X0) = X3 ),
% 7.81/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_796,plain,
% 7.81/1.49      ( k10_lattice3(X0,X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,X0,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X1,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X2,sK1(X2,X1,X0,X3)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_13,plain,
% 7.81/1.49      ( ~ sP0(X0,X1,X2,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X0,X3)
% 7.81/1.49      | ~ r1_orders_2(X2,X1,X3)
% 7.81/1.49      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2))
% 7.81/1.49      | k10_lattice3(X2,X1,X0) = X3 ),
% 7.81/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_794,plain,
% 7.81/1.49      ( k10_lattice3(X0,X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,X0,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(sK1(X2,X1,X0,X3),u1_struct_0(X0)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1824,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(sK1(X2,X1,k2_yellow_1(X0),X3),X0) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_23,c_794]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4,plain,
% 7.81/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.81/1.49      | r3_orders_2(X0,X1,X2)
% 7.81/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.81/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.81/1.49      | v2_struct_0(X0)
% 7.81/1.49      | ~ v3_orders_2(X0)
% 7.81/1.49      | ~ l1_orders_2(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_803,plain,
% 7.81/1.49      ( r1_orders_2(X0,X1,X2) != iProver_top
% 7.81/1.49      | r3_orders_2(X0,X1,X2) = iProver_top
% 7.81/1.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | v2_struct_0(X0) = iProver_top
% 7.81/1.49      | v3_orders_2(X0) != iProver_top
% 7.81/1.49      | l1_orders_2(X0) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3028,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(u1_struct_0(X0)),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(u1_struct_0(X0)),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(X0,X4,sK1(X2,X1,k2_yellow_1(u1_struct_0(X0)),X3)) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(u1_struct_0(X0)),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(u1_struct_0(X0)),X1,X3) != iProver_top
% 7.81/1.49      | r3_orders_2(X0,X4,sK1(X2,X1,k2_yellow_1(u1_struct_0(X0)),X3)) = iProver_top
% 7.81/1.49      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 7.81/1.49      | v2_struct_0(X0) = iProver_top
% 7.81/1.49      | v3_orders_2(X0) != iProver_top
% 7.81/1.49      | l1_orders_2(X0) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1824,c_803]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10531,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X1,X3) != iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(u1_struct_0(k2_yellow_1(X0))),X3)) = iProver_top
% 7.81/1.49      | m1_subset_1(X4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top
% 7.81/1.49      | v3_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_23,c_3028]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10542,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | m1_subset_1(X4,X0) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top
% 7.81/1.49      | v3_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.49      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_10531,c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10625,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),X4,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | m1_subset_1(X4,X0) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_10542,c_46,c_52]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10642,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),X2,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_796,c_10625]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25,plain,
% 7.81/1.49      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 7.81/1.49      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.49      | r1_tarski(X1,X2)
% 7.81/1.49      | v1_xboole_0(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_784,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.49      | r1_tarski(X1,X2) = iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_847,plain,
% 7.81/1.49      ( r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X1,X2) = iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_784,c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10849,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(sK1(X2,X1,k2_yellow_1(X0),X3),X0) != iProver_top
% 7.81/1.49      | r1_tarski(X2,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_10642,c_847]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_12233,plain,
% 7.81/1.49      ( v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | r1_tarski(X2,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_10849,c_43,c_1824]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_12234,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X2,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(renaming,[status(thm)],[c_12233]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10641,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | r3_orders_2(k2_yellow_1(X0),X1,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_795,c_10625]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10777,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(sK1(X2,X1,k2_yellow_1(X0),X3),X0) != iProver_top
% 7.81/1.49      | r1_tarski(X1,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_10641,c_847]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_12204,plain,
% 7.81/1.49      ( v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | r1_tarski(X1,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_10777,c_43,c_1824]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_12205,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.49      | r1_tarski(X1,sK1(X2,X1,k2_yellow_1(X0),X3)) = iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(renaming,[status(thm)],[c_12204]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4832,plain,
% 7.81/1.49      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | m1_subset_1(X3,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(sK1(X2,X1,k2_yellow_1(X0),X3),X0) != iProver_top
% 7.81/1.49      | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_4821,c_797]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_11901,plain,
% 7.81/1.49      ( m1_subset_1(X3,X0) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.49      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.49      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.49      | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.50      | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(global_propositional_subsumption,
% 7.81/1.50                [status(thm)],
% 7.81/1.50                [c_4832,c_1824]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_11902,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
% 7.81/1.50      | sP0(X2,X1,k2_yellow_1(X0),X3) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,X3) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,X3) != iProver_top
% 7.81/1.50      | m1_subset_1(X3,X0) != iProver_top
% 7.81/1.50      | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),X3)) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(renaming,[status(thm)],[c_11901]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_11914,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X3,X4)
% 7.81/1.50      | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X3,X4)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X3,X4)) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X3,X4),X0) != iProver_top
% 7.81/1.50      | r1_tarski(X4,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4))) != iProver_top
% 7.81/1.50      | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4))) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_805,c_11902]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_18155,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X3,X4)
% 7.81/1.50      | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X3,X4)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X3,X4)) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X3,X4),X0) != iProver_top
% 7.81/1.50      | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X4))) != iProver_top
% 7.81/1.50      | r1_tarski(X4,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X4,X3))) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_0,c_11914]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_18304,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X3)
% 7.81/1.50      | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X1,X3)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X3)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X3)) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X3),X0) != iProver_top
% 7.81/1.50      | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X3,X1))) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_12205,c_18155]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_19128,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X3)
% 7.81/1.50      | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X1,X3)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X3)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X3)) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X3),X0) != iProver_top
% 7.81/1.50      | r1_tarski(X3,sK1(X2,X1,k2_yellow_1(X0),k2_xboole_0(X1,X3))) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_0,c_18304]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_19380,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 7.81/1.50      | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_12234,c_19128]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_19432,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 7.81/1.50      | sP0(X2,X1,k2_yellow_1(X0),k2_xboole_0(X2,X1)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_0,c_19380]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_19431,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.50      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X2),u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top
% 7.81/1.50      | v5_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.50      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_793,c_19380]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_19462,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top
% 7.81/1.50      | v5_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.50      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_19431,c_23]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_19756,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(global_propositional_subsumption,
% 7.81/1.50                [status(thm)],
% 7.81/1.50                [c_19432,c_49,c_52,c_19462]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_19771,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X1,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.50      | r1_orders_2(k2_yellow_1(X0),X2,k2_xboole_0(X2,X1)) != iProver_top
% 7.81/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(X1,X2),X0) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_0,c_19756]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_22020,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(sK2),sK3,sK4) = k2_xboole_0(sK3,sK4)
% 7.81/1.50      | r1_orders_2(k2_yellow_1(sK2),sK3,k2_xboole_0(sK3,sK4)) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top
% 7.81/1.50      | m1_subset_1(sK4,sK2) != iProver_top
% 7.81/1.50      | m1_subset_1(sK3,sK2) != iProver_top
% 7.81/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_22010,c_19771]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_29,negated_conjecture,
% 7.81/1.50      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
% 7.81/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_32,plain,
% 7.81/1.50      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
% 7.81/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_781,plain,
% 7.81/1.50      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
% 7.81/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_819,plain,
% 7.81/1.50      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_781,c_23]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_258,plain,( X0 = X0 ),theory(equality) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_1326,plain,
% 7.81/1.50      ( k2_xboole_0(sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_258]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_1988,plain,
% 7.81/1.50      ( r3_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4))
% 7.81/1.50      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.50      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.50      | ~ r1_tarski(sK3,k2_xboole_0(sK3,sK4))
% 7.81/1.50      | v1_xboole_0(X0) ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_1203]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_1993,plain,
% 7.81/1.50      ( r3_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4)) = iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.50      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.50      | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top
% 7.81/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.50      inference(predicate_to_equality,[status(thm)],[c_1988]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_1995,plain,
% 7.81/1.50      ( r3_orders_2(k2_yellow_1(sK2),sK3,k2_xboole_0(sK3,sK4)) = iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 7.81/1.50      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 7.81/1.50      | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top
% 7.81/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_1993]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_1553,plain,
% 7.81/1.50      ( m1_subset_1(k2_xboole_0(sK3,sK4),X0)
% 7.81/1.50      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
% 7.81/1.50      | X0 != sK2
% 7.81/1.50      | k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4) ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_1258]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_2019,plain,
% 7.81/1.50      ( m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.50      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),sK2)
% 7.81/1.50      | k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4)
% 7.81/1.50      | u1_struct_0(k2_yellow_1(X0)) != sK2 ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_1553]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_2021,plain,
% 7.81/1.50      ( k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4)
% 7.81/1.50      | u1_struct_0(k2_yellow_1(X0)) != sK2
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0))) = iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
% 7.81/1.50      inference(predicate_to_equality,[status(thm)],[c_2019]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_2023,plain,
% 7.81/1.50      ( k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4)
% 7.81/1.50      | u1_struct_0(k2_yellow_1(sK2)) != sK2
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) = iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_2021]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_3342,plain,
% 7.81/1.50      ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_3343,plain,
% 7.81/1.50      ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) = iProver_top ),
% 7.81/1.50      inference(predicate_to_equality,[status(thm)],[c_3342]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_16678,plain,
% 7.81/1.50      ( r1_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4))
% 7.81/1.50      | ~ r3_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4))
% 7.81/1.50      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.50      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
% 7.81/1.50      | v2_struct_0(k2_yellow_1(X0))
% 7.81/1.50      | ~ v3_orders_2(k2_yellow_1(X0))
% 7.81/1.50      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_16684,plain,
% 7.81/1.50      ( r1_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4)) = iProver_top
% 7.81/1.50      | r3_orders_2(k2_yellow_1(X0),sK3,k2_xboole_0(sK3,sK4)) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.50      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 7.81/1.50      | v2_struct_0(k2_yellow_1(X0)) = iProver_top
% 7.81/1.50      | v3_orders_2(k2_yellow_1(X0)) != iProver_top
% 7.81/1.50      | l1_orders_2(k2_yellow_1(X0)) != iProver_top ),
% 7.81/1.50      inference(predicate_to_equality,[status(thm)],[c_16678]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_16686,plain,
% 7.81/1.50      ( r1_orders_2(k2_yellow_1(sK2),sK3,k2_xboole_0(sK3,sK4)) = iProver_top
% 7.81/1.50      | r3_orders_2(k2_yellow_1(sK2),sK3,k2_xboole_0(sK3,sK4)) != iProver_top
% 7.81/1.50      | m1_subset_1(k2_xboole_0(sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 7.81/1.50      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 7.81/1.50      | v2_struct_0(k2_yellow_1(sK2)) = iProver_top
% 7.81/1.50      | v3_orders_2(k2_yellow_1(sK2)) != iProver_top
% 7.81/1.50      | l1_orders_2(k2_yellow_1(sK2)) != iProver_top ),
% 7.81/1.50      inference(instantiation,[status(thm)],[c_16684]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_31845,plain,
% 7.81/1.50      ( k10_lattice3(k2_yellow_1(sK2),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 7.81/1.50      inference(global_propositional_subsumption,
% 7.81/1.50                [status(thm)],
% 7.81/1.50                [c_22020,c_31,c_32,c_34,c_41,c_45,c_48,c_54,c_822,c_819,
% 7.81/1.50                 c_1132,c_1326,c_1995,c_2023,c_3343,c_16686]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_26,negated_conjecture,
% 7.81/1.50      ( k2_xboole_0(sK3,sK4) != k10_lattice3(k2_yellow_1(sK2),sK3,sK4) ),
% 7.81/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_31848,plain,
% 7.81/1.50      ( k2_xboole_0(sK3,sK4) != k2_xboole_0(sK3,sK4) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_31845,c_26]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(contradiction,plain,
% 7.81/1.50      ( $false ),
% 7.81/1.50      inference(minisat,[status(thm)],[c_31848,c_1326]) ).
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.50  
% 7.81/1.50  ------                               Statistics
% 7.81/1.50  
% 7.81/1.50  ------ Selected
% 7.81/1.50  
% 7.81/1.50  total_time:                             0.934
% 7.81/1.50  
%------------------------------------------------------------------------------
