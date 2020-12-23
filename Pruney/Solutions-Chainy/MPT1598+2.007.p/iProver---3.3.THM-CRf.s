%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:06 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 302 expanded)
%              Number of clauses        :   81 ( 111 expanded)
%              Number of leaves         :   18 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  626 (1404 expanded)
%              Number of equality atoms :   68 (  82 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   4 average)
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

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k2_xboole_0(X1,sK3),k10_lattice3(k2_yellow_1(X0),X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_xboole_0(sK2,X2),k10_lattice3(k2_yellow_1(X0),sK2,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
        & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v1_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK1),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) )
      & v1_lattice3(k2_yellow_1(sK1))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v1_lattice3(k2_yellow_1(sK1))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f39,f38,f37])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f60,plain,(
    v1_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f63,plain,(
    ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f40])).

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
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_340,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_12,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_344,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_12])).

cnf(c_345,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_344])).

cnf(c_1056,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0_50),X0_47,X1_47)
    | r3_orders_2(k2_yellow_1(X0_50),X0_47,X1_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50)))
    | v2_struct_0(k2_yellow_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_345])).

cnf(c_1446,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),X0_47,X1_47)
    | r3_orders_2(k2_yellow_1(sK1),X0_47,X1_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1579,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47))
    | r3_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_10752,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_786,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_787,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k10_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_1047,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50)))
    | m1_subset_1(k10_lattice3(k2_yellow_1(X0_50),X0_47,X1_47),u1_struct_0(k2_yellow_1(X0_50))) ),
    inference(subtyping,[status(esa)],[c_787])).

cnf(c_10671,plain,
    ( m1_subset_1(k10_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1047])).

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
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_258,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_1060,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0_47,X1_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_1625,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_7320,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_1546,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
    | r3_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47),u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_7225,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_1615,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47),u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47)) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_7182,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_21,negated_conjecture,
    ( v1_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_506,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_507,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1)))
    | ~ v5_orders_2(k2_yellow_1(sK1))
    | ~ l1_orders_2(k2_yellow_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_13,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_41,plain,
    ( v5_orders_2(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_44,plain,
    ( l1_orders_2(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_511,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_41,c_44])).

cnf(c_1055,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_511])).

cnf(c_5546,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_1071,plain,
    ( ~ m1_subset_1(X0_47,X0_48)
    | m1_subset_1(X1_47,X0_48)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_1459,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1_47,X2_47),u1_struct_0(k2_yellow_1(sK1)))
    | k13_lattice3(k2_yellow_1(sK1),X1_47,X2_47) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_1486,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
    | k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47) != k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_5531,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | k13_lattice3(k2_yellow_1(sK1),sK2,sK3) != k10_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_530,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_531,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1,X0),u1_struct_0(k2_yellow_1(sK1)))
    | ~ v5_orders_2(k2_yellow_1(sK1))
    | ~ l1_orders_2(k2_yellow_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_533,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1,X0),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_41,c_44])).

cnf(c_1054,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47),u1_struct_0(k2_yellow_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_533])).

cnf(c_5459,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1064,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | ~ r1_tarski(X2_47,X1_47)
    | r1_tarski(k2_xboole_0(X2_47,X0_47),X1_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1801,plain,
    ( ~ r1_tarski(X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
    | ~ r1_tarski(X2_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
    | r1_tarski(k2_xboole_0(X2_47,X0_47),k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47)) ),
    inference(instantiation,[status(thm)],[c_1064])).

cnf(c_5405,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_1069,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_1441,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) != X1_47
    | k2_xboole_0(sK2,sK3) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1474,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),X0_47)
    | r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) != X0_47
    | k2_xboole_0(sK2,sK3) != k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_4394,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) != k13_lattice3(k2_yellow_1(sK1),sK2,sK3)
    | k2_xboole_0(sK2,sK3) != k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_1067,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1633,plain,
    ( X0_47 != X1_47
    | X0_47 = k13_lattice3(k2_yellow_1(sK1),X2_47,X3_47)
    | k13_lattice3(k2_yellow_1(sK1),X2_47,X3_47) != X1_47 ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_1816,plain,
    ( X0_47 = k13_lattice3(k2_yellow_1(sK1),X1_47,X2_47)
    | X0_47 != k10_lattice3(k2_yellow_1(sK1),X1_47,X2_47)
    | k13_lattice3(k2_yellow_1(sK1),X1_47,X2_47) != k10_lattice3(k2_yellow_1(sK1),X1_47,X2_47) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_1908,plain,
    ( k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47) != k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47)
    | k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47) = k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47)
    | k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47) != k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47) ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_2523,plain,
    ( k13_lattice3(k2_yellow_1(sK1),sK2,sK3) != k10_lattice3(k2_yellow_1(sK1),sK2,sK3)
    | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3)
    | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) != k10_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_1066,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1798,plain,
    ( k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k10_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1066])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1062,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1390,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | k2_yellow_1(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v5_orders_2(k2_yellow_1(sK1))
    | ~ l1_orders_2(k2_yellow_1(sK1))
    | k13_lattice3(k2_yellow_1(sK1),X0,X1) = k10_lattice3(k2_yellow_1(sK1),X0,X1) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | k13_lattice3(k2_yellow_1(sK1),X0,X1) = k10_lattice3(k2_yellow_1(sK1),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_41,c_44])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | k13_lattice3(k2_yellow_1(sK1),X1,X0) = k10_lattice3(k2_yellow_1(sK1),X1,X0) ),
    inference(renaming,[status(thm)],[c_716])).

cnf(c_1048,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
    | k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47) = k10_lattice3(k2_yellow_1(sK1),X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_717])).

cnf(c_1404,plain,
    ( k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47) = k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1048])).

cnf(c_1536,plain,
    ( k13_lattice3(k2_yellow_1(sK1),X0_47,sK3) = k10_lattice3(k2_yellow_1(sK1),X0_47,sK3)
    | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1404])).

cnf(c_1539,plain,
    ( k13_lattice3(k2_yellow_1(sK1),sK2,sK3) = k10_lattice3(k2_yellow_1(sK1),sK2,sK3)
    | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_1532,plain,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1066])).

cnf(c_15,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_35,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10752,c_10671,c_7320,c_7225,c_7182,c_5546,c_5531,c_5459,c_5405,c_4394,c_2523,c_1798,c_1539,c_1532,c_35,c_18,c_19,c_25,c_20,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/0.99  
% 4.02/0.99  ------  iProver source info
% 4.02/0.99  
% 4.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/0.99  git: non_committed_changes: false
% 4.02/0.99  git: last_make_outside_of_git: false
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    ""
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         true
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     num_symb
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       true
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     true
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_input_bw                          []
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  ------ Parsing...
% 4.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.99  ------ Proving...
% 4.02/0.99  ------ Problem Properties 
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  clauses                                 18
% 4.02/0.99  conjectures                             3
% 4.02/0.99  EPR                                     0
% 4.02/0.99  Horn                                    13
% 4.02/0.99  unary                                   4
% 4.02/0.99  binary                                  0
% 4.02/0.99  lits                                    74
% 4.02/0.99  lits eq                                 5
% 4.02/0.99  fd_pure                                 0
% 4.02/0.99  fd_pseudo                               0
% 4.02/0.99  fd_cond                                 0
% 4.02/0.99  fd_pseudo_cond                          4
% 4.02/0.99  AC symbols                              0
% 4.02/0.99  
% 4.02/0.99  ------ Schedule dynamic 5 is on 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  Current options:
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    ""
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         true
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     none
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       false
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     true
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_input_bw                          []
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ Proving...
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS status Theorem for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  fof(f2,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f18,plain,(
% 4.02/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f2])).
% 4.02/0.99  
% 4.02/0.99  fof(f19,plain,(
% 4.02/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(flattening,[],[f18])).
% 4.02/0.99  
% 4.02/0.99  fof(f30,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(nnf_transformation,[],[f19])).
% 4.02/0.99  
% 4.02/0.99  fof(f43,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f30])).
% 4.02/0.99  
% 4.02/0.99  fof(f7,axiom,(
% 4.02/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f12,plain,(
% 4.02/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 4.02/0.99    inference(pure_predicate_removal,[],[f7])).
% 4.02/0.99  
% 4.02/0.99  fof(f14,plain,(
% 4.02/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 4.02/0.99    inference(pure_predicate_removal,[],[f12])).
% 4.02/0.99  
% 4.02/0.99  fof(f54,plain,(
% 4.02/0.99    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f14])).
% 4.02/0.99  
% 4.02/0.99  fof(f6,axiom,(
% 4.02/0.99    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f13,plain,(
% 4.02/0.99    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 4.02/0.99    inference(pure_predicate_removal,[],[f6])).
% 4.02/0.99  
% 4.02/0.99  fof(f53,plain,(
% 4.02/0.99    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f13])).
% 4.02/0.99  
% 4.02/0.99  fof(f3,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f20,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f3])).
% 4.02/0.99  
% 4.02/0.99  fof(f21,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 4.02/0.99    inference(flattening,[],[f20])).
% 4.02/0.99  
% 4.02/0.99  fof(f44,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f21])).
% 4.02/0.99  
% 4.02/0.99  fof(f9,axiom,(
% 4.02/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f27,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f9])).
% 4.02/0.99  
% 4.02/0.99  fof(f36,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 4.02/0.99    inference(nnf_transformation,[],[f27])).
% 4.02/0.99  
% 4.02/0.99  fof(f57,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f36])).
% 4.02/0.99  
% 4.02/0.99  fof(f10,conjecture,(
% 4.02/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f11,negated_conjecture,(
% 4.02/0.99    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 4.02/0.99    inference(negated_conjecture,[],[f10])).
% 4.02/0.99  
% 4.02/0.99  fof(f28,plain,(
% 4.02/0.99    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f11])).
% 4.02/0.99  
% 4.02/0.99  fof(f29,plain,(
% 4.02/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 4.02/0.99    inference(flattening,[],[f28])).
% 4.02/0.99  
% 4.02/0.99  fof(f39,plain,(
% 4.02/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k2_xboole_0(X1,sK3),k10_lattice3(k2_yellow_1(X0),X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f38,plain,(
% 4.02/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK2,X2),k10_lattice3(k2_yellow_1(X0),sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f37,plain,(
% 4.02/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK1),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v1_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f40,plain,(
% 4.02/0.99    ((~r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v1_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f39,f38,f37])).
% 4.02/0.99  
% 4.02/0.99  fof(f59,plain,(
% 4.02/0.99    ~v1_xboole_0(sK1)),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f5,axiom,(
% 4.02/0.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f24,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f5])).
% 4.02/0.99  
% 4.02/0.99  fof(f25,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 4.02/0.99    inference(flattening,[],[f24])).
% 4.02/0.99  
% 4.02/0.99  fof(f31,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 4.02/0.99    inference(nnf_transformation,[],[f25])).
% 4.02/0.99  
% 4.02/0.99  fof(f32,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 4.02/0.99    inference(flattening,[],[f31])).
% 4.02/0.99  
% 4.02/0.99  fof(f33,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 4.02/0.99    inference(rectify,[],[f32])).
% 4.02/0.99  
% 4.02/0.99  fof(f34,plain,(
% 4.02/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f35,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 4.02/0.99  
% 4.02/0.99  fof(f46,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f35])).
% 4.02/0.99  
% 4.02/0.99  fof(f66,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 4.02/0.99    inference(equality_resolution,[],[f46])).
% 4.02/0.99  
% 4.02/0.99  fof(f60,plain,(
% 4.02/0.99    v1_lattice3(k2_yellow_1(sK1))),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f55,plain,(
% 4.02/0.99    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f14])).
% 4.02/0.99  
% 4.02/0.99  fof(f47,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f35])).
% 4.02/0.99  
% 4.02/0.99  fof(f65,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 4.02/0.99    inference(equality_resolution,[],[f47])).
% 4.02/0.99  
% 4.02/0.99  fof(f1,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f16,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 4.02/0.99    inference(ennf_transformation,[],[f1])).
% 4.02/0.99  
% 4.02/0.99  fof(f17,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 4.02/0.99    inference(flattening,[],[f16])).
% 4.02/0.99  
% 4.02/0.99  fof(f41,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f17])).
% 4.02/0.99  
% 4.02/0.99  fof(f62,plain,(
% 4.02/0.99    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f4,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f22,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f4])).
% 4.02/0.99  
% 4.02/0.99  fof(f23,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 4.02/0.99    inference(flattening,[],[f22])).
% 4.02/0.99  
% 4.02/0.99  fof(f45,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f23])).
% 4.02/0.99  
% 4.02/0.99  fof(f8,axiom,(
% 4.02/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f15,plain,(
% 4.02/0.99    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 4.02/0.99    inference(pure_predicate_removal,[],[f8])).
% 4.02/0.99  
% 4.02/0.99  fof(f26,plain,(
% 4.02/0.99    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f15])).
% 4.02/0.99  
% 4.02/0.99  fof(f56,plain,(
% 4.02/0.99    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f26])).
% 4.02/0.99  
% 4.02/0.99  fof(f63,plain,(
% 4.02/0.99    ~r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f61,plain,(
% 4.02/0.99    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1,plain,
% 4.02/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 4.02/0.99      | r3_orders_2(X0,X1,X2)
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.02/0.99      | v2_struct_0(X0)
% 4.02/0.99      | ~ v3_orders_2(X0)
% 4.02/0.99      | ~ l1_orders_2(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_14,plain,
% 4.02/0.99      ( v3_orders_2(k2_yellow_1(X0)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_339,plain,
% 4.02/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 4.02/0.99      | r3_orders_2(X0,X1,X2)
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.02/0.99      | v2_struct_0(X0)
% 4.02/0.99      | ~ l1_orders_2(X0)
% 4.02/0.99      | k2_yellow_1(X3) != X0 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_340,plain,
% 4.02/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 4.02/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | v2_struct_0(k2_yellow_1(X0))
% 4.02/0.99      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12,plain,
% 4.02/0.99      ( l1_orders_2(k2_yellow_1(X0)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_344,plain,
% 4.02/0.99      ( v2_struct_0(k2_yellow_1(X0))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 4.02/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_340,c_12]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_345,plain,
% 4.02/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 4.02/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_344]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1056,plain,
% 4.02/0.99      ( ~ r1_orders_2(k2_yellow_1(X0_50),X0_47,X1_47)
% 4.02/0.99      | r3_orders_2(k2_yellow_1(X0_50),X0_47,X1_47)
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50)))
% 4.02/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50)))
% 4.02/0.99      | v2_struct_0(k2_yellow_1(X0_50)) ),
% 4.02/0.99      inference(subtyping,[status(esa)],[c_345]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1446,plain,
% 4.02/0.99      ( ~ r1_orders_2(k2_yellow_1(sK1),X0_47,X1_47)
% 4.02/0.99      | r3_orders_2(k2_yellow_1(sK1),X0_47,X1_47)
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | v2_struct_0(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1056]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1579,plain,
% 4.02/0.99      ( ~ r1_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47))
% 4.02/0.99      | r3_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47))
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | v2_struct_0(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1446]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10752,plain,
% 4.02/0.99      ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | v2_struct_0(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1579]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.02/0.99      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 4.02/0.99      | ~ l1_orders_2(X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_786,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.02/0.99      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 4.02/0.99      | k2_yellow_1(X3) != X1 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_787,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 4.02/0.99      | m1_subset_1(k10_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_786]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1047,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(X0_50)))
% 4.02/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(X0_50)))
% 4.02/0.99      | m1_subset_1(k10_lattice3(k2_yellow_1(X0_50),X0_47,X1_47),u1_struct_0(k2_yellow_1(X0_50))) ),
% 4.02/0.99      inference(subtyping,[status(esa)],[c_787]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10671,plain,
% 4.02/0.99      ( m1_subset_1(k10_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1047]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_17,plain,
% 4.02/0.99      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | r1_tarski(X1,X2)
% 4.02/0.99      | v1_xboole_0(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_22,negated_conjecture,
% 4.02/0.99      ( ~ v1_xboole_0(sK1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_257,plain,
% 4.02/0.99      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 4.02/0.99      | r1_tarski(X1,X2)
% 4.02/0.99      | sK1 != X0 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_258,plain,
% 4.02/0.99      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | r1_tarski(X0,X1) ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_257]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1060,plain,
% 4.02/0.99      ( ~ r3_orders_2(k2_yellow_1(sK1),X0_47,X1_47)
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | r1_tarski(X0_47,X1_47) ),
% 4.02/0.99      inference(subtyping,[status(esa)],[c_258]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1625,plain,
% 4.02/0.99      ( ~ r3_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47))
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | r1_tarski(X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1060]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7320,plain,
% 4.02/0.99      ( ~ r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1625]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1546,plain,
% 4.02/0.99      ( ~ r1_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
% 4.02/0.99      | r3_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | v2_struct_0(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1446]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7225,plain,
% 4.02/0.99      ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | v2_struct_0(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1546]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1615,plain,
% 4.02/0.99      ( ~ r3_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | r1_tarski(X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1060]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7182,plain,
% 4.02/0.99      ( ~ r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1615]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_11,plain,
% 4.02/0.99      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
% 4.02/0.99      | ~ v5_orders_2(X0)
% 4.02/0.99      | ~ v1_lattice3(X0)
% 4.02/0.99      | ~ l1_orders_2(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f66]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_21,negated_conjecture,
% 4.02/0.99      ( v1_lattice3(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_506,plain,
% 4.02/0.99      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
% 4.02/0.99      | ~ v5_orders_2(X0)
% 4.02/0.99      | ~ l1_orders_2(X0)
% 4.02/0.99      | k2_yellow_1(sK1) != X0 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_507,plain,
% 4.02/0.99      ( r1_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),X0,X1))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ v5_orders_2(k2_yellow_1(sK1))
% 4.02/0.99      | ~ l1_orders_2(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_506]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_13,plain,
% 4.02/0.99      ( v5_orders_2(k2_yellow_1(X0)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_41,plain,
% 4.02/0.99      ( v5_orders_2(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_44,plain,
% 4.02/0.99      ( l1_orders_2(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_511,plain,
% 4.02/0.99      ( r1_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),X0,X1))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0,X1),u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_507,c_41,c_44]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1055,plain,
% 4.02/0.99      ( r1_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47))
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(subtyping,[status(esa)],[c_511]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5546,plain,
% 4.02/0.99      ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1055]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1071,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0_47,X0_48)
% 4.02/0.99      | m1_subset_1(X1_47,X0_48)
% 4.02/0.99      | X1_47 != X0_47 ),
% 4.02/0.99      theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1459,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1_47,X2_47),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),X1_47,X2_47) != X0_47 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1071]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1486,plain,
% 4.02/0.99      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47) != k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1459]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5531,plain,
% 4.02/0.99      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),sK2,sK3) != k10_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1486]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10,plain,
% 4.02/0.99      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
% 4.02/0.99      | ~ v5_orders_2(X0)
% 4.02/0.99      | ~ v1_lattice3(X0)
% 4.02/0.99      | ~ l1_orders_2(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_530,plain,
% 4.02/0.99      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
% 4.02/0.99      | ~ v5_orders_2(X0)
% 4.02/0.99      | ~ l1_orders_2(X0)
% 4.02/0.99      | k2_yellow_1(sK1) != X0 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_531,plain,
% 4.02/0.99      ( r1_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),X1,X0))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1,X0),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ v5_orders_2(k2_yellow_1(sK1))
% 4.02/0.99      | ~ l1_orders_2(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_530]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_533,plain,
% 4.02/0.99      ( r1_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),X1,X0))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1,X0),u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_531,c_41,c_44]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1054,plain,
% 4.02/0.99      ( r1_orders_2(k2_yellow_1(sK1),X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
% 4.02/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47),u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(subtyping,[status(esa)],[c_533]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5459,plain,
% 4.02/0.99      ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1054]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_0,plain,
% 4.02/0.99      ( ~ r1_tarski(X0,X1)
% 4.02/0.99      | ~ r1_tarski(X2,X1)
% 4.02/0.99      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f41]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1064,plain,
% 4.02/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 4.02/0.99      | ~ r1_tarski(X2_47,X1_47)
% 4.02/0.99      | r1_tarski(k2_xboole_0(X2_47,X0_47),X1_47) ),
% 4.02/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1801,plain,
% 4.02/0.99      ( ~ r1_tarski(X0_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
% 4.02/0.99      | ~ r1_tarski(X2_47,k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47))
% 4.02/0.99      | r1_tarski(k2_xboole_0(X2_47,X0_47),k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1064]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5405,plain,
% 4.02/0.99      ( r1_tarski(k2_xboole_0(sK2,sK3),k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | ~ r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1801]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1069,plain,
% 4.02/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 4.02/0.99      | r1_tarski(X2_47,X3_47)
% 4.02/0.99      | X2_47 != X0_47
% 4.02/0.99      | X3_47 != X1_47 ),
% 4.02/0.99      theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1441,plain,
% 4.02/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 4.02/0.99      | r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) != X1_47
% 4.02/0.99      | k2_xboole_0(sK2,sK3) != X0_47 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1069]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1474,plain,
% 4.02/0.99      ( ~ r1_tarski(k2_xboole_0(sK2,sK3),X0_47)
% 4.02/0.99      | r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) != X0_47
% 4.02/0.99      | k2_xboole_0(sK2,sK3) != k2_xboole_0(sK2,sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1441]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4394,plain,
% 4.02/0.99      ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 4.02/0.99      | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) != k13_lattice3(k2_yellow_1(sK1),sK2,sK3)
% 4.02/0.99      | k2_xboole_0(sK2,sK3) != k2_xboole_0(sK2,sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1474]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1067,plain,
% 4.02/0.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 4.02/0.99      theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1633,plain,
% 4.02/0.99      ( X0_47 != X1_47
% 4.02/0.99      | X0_47 = k13_lattice3(k2_yellow_1(sK1),X2_47,X3_47)
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),X2_47,X3_47) != X1_47 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1067]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1816,plain,
% 4.02/0.99      ( X0_47 = k13_lattice3(k2_yellow_1(sK1),X1_47,X2_47)
% 4.02/0.99      | X0_47 != k10_lattice3(k2_yellow_1(sK1),X1_47,X2_47)
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),X1_47,X2_47) != k10_lattice3(k2_yellow_1(sK1),X1_47,X2_47) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1633]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1908,plain,
% 4.02/0.99      ( k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47) != k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47)
% 4.02/0.99      | k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47) = k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47)
% 4.02/0.99      | k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47) != k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1816]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2523,plain,
% 4.02/0.99      ( k13_lattice3(k2_yellow_1(sK1),sK2,sK3) != k10_lattice3(k2_yellow_1(sK1),sK2,sK3)
% 4.02/0.99      | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3)
% 4.02/0.99      | k10_lattice3(k2_yellow_1(sK1),sK2,sK3) != k10_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1908]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1066,plain,( X0_47 = X0_47 ),theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1798,plain,
% 4.02/0.99      ( k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k10_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1066]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_19,negated_conjecture,
% 4.02/0.99      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f62]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1062,negated_conjecture,
% 4.02/0.99      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1390,plain,
% 4.02/0.99      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1062]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.02/0.99      | ~ v5_orders_2(X1)
% 4.02/0.99      | ~ v1_lattice3(X1)
% 4.02/0.99      | ~ l1_orders_2(X1)
% 4.02/0.99      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_711,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.02/0.99      | ~ v5_orders_2(X1)
% 4.02/0.99      | ~ l1_orders_2(X1)
% 4.02/0.99      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
% 4.02/0.99      | k2_yellow_1(sK1) != X1 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_712,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ v5_orders_2(k2_yellow_1(sK1))
% 4.02/0.99      | ~ l1_orders_2(k2_yellow_1(sK1))
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),X0,X1) = k10_lattice3(k2_yellow_1(sK1),X0,X1) ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_711]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_716,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),X0,X1) = k10_lattice3(k2_yellow_1(sK1),X0,X1) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_712,c_41,c_44]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_717,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),X1,X0) = k10_lattice3(k2_yellow_1(sK1),X1,X0) ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_716]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1048,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1)))
% 4.02/0.99      | k13_lattice3(k2_yellow_1(sK1),X1_47,X0_47) = k10_lattice3(k2_yellow_1(sK1),X1_47,X0_47) ),
% 4.02/0.99      inference(subtyping,[status(esa)],[c_717]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1404,plain,
% 4.02/0.99      ( k13_lattice3(k2_yellow_1(sK1),X0_47,X1_47) = k10_lattice3(k2_yellow_1(sK1),X0_47,X1_47)
% 4.02/0.99      | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 4.02/0.99      | m1_subset_1(X1_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1048]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1536,plain,
% 4.02/0.99      ( k13_lattice3(k2_yellow_1(sK1),X0_47,sK3) = k10_lattice3(k2_yellow_1(sK1),X0_47,sK3)
% 4.02/0.99      | m1_subset_1(X0_47,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1390,c_1404]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1539,plain,
% 4.02/0.99      ( k13_lattice3(k2_yellow_1(sK1),sK2,sK3) = k10_lattice3(k2_yellow_1(sK1),sK2,sK3)
% 4.02/0.99      | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1536]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1532,plain,
% 4.02/0.99      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1066]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_15,plain,
% 4.02/0.99      ( v1_xboole_0(X0) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_35,plain,
% 4.02/0.99      ( v1_xboole_0(sK1) | ~ v2_struct_0(k2_yellow_1(sK1)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_18,negated_conjecture,
% 4.02/0.99      ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_20,negated_conjecture,
% 4.02/0.99      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_25,plain,
% 4.02/0.99      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(contradiction,plain,
% 4.02/0.99      ( $false ),
% 4.02/0.99      inference(minisat,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_10752,c_10671,c_7320,c_7225,c_7182,c_5546,c_5531,
% 4.02/0.99                 c_5459,c_5405,c_4394,c_2523,c_1798,c_1539,c_1532,c_35,
% 4.02/0.99                 c_18,c_19,c_25,c_20,c_22]) ).
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  ------                               Statistics
% 4.02/0.99  
% 4.02/0.99  ------ General
% 4.02/0.99  
% 4.02/0.99  abstr_ref_over_cycles:                  0
% 4.02/0.99  abstr_ref_under_cycles:                 0
% 4.02/0.99  gc_basic_clause_elim:                   0
% 4.02/0.99  forced_gc_time:                         0
% 4.02/0.99  parsing_time:                           0.01
% 4.02/0.99  unif_index_cands_time:                  0.
% 4.02/0.99  unif_index_add_time:                    0.
% 4.02/0.99  orderings_time:                         0.
% 4.02/0.99  out_proof_time:                         0.011
% 4.02/0.99  total_time:                             0.368
% 4.02/0.99  num_of_symbols:                         54
% 4.02/0.99  num_of_terms:                           10734
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing
% 4.02/0.99  
% 4.02/0.99  num_of_splits:                          0
% 4.02/0.99  num_of_split_atoms:                     0
% 4.02/0.99  num_of_reused_defs:                     0
% 4.02/0.99  num_eq_ax_congr_red:                    33
% 4.02/0.99  num_of_sem_filtered_clauses:            1
% 4.02/0.99  num_of_subtypes:                        4
% 4.02/0.99  monotx_restored_types:                  0
% 4.02/0.99  sat_num_of_epr_types:                   0
% 4.02/0.99  sat_num_of_non_cyclic_types:            0
% 4.02/0.99  sat_guarded_non_collapsed_types:        1
% 4.02/0.99  num_pure_diseq_elim:                    0
% 4.02/0.99  simp_replaced_by:                       0
% 4.02/0.99  res_preprocessed:                       92
% 4.02/0.99  prep_upred:                             0
% 4.02/0.99  prep_unflattend:                        22
% 4.02/0.99  smt_new_axioms:                         0
% 4.02/0.99  pred_elim_cands:                        5
% 4.02/0.99  pred_elim:                              5
% 4.02/0.99  pred_elim_cl:                           5
% 4.02/0.99  pred_elim_cycles:                       10
% 4.02/0.99  merged_defs:                            0
% 4.02/0.99  merged_defs_ncl:                        0
% 4.02/0.99  bin_hyper_res:                          0
% 4.02/0.99  prep_cycles:                            4
% 4.02/0.99  pred_elim_time:                         0.015
% 4.02/0.99  splitting_time:                         0.
% 4.02/0.99  sem_filter_time:                        0.
% 4.02/0.99  monotx_time:                            0.
% 4.02/0.99  subtype_inf_time:                       0.
% 4.02/0.99  
% 4.02/0.99  ------ Problem properties
% 4.02/0.99  
% 4.02/0.99  clauses:                                18
% 4.02/0.99  conjectures:                            3
% 4.02/0.99  epr:                                    0
% 4.02/0.99  horn:                                   13
% 4.02/0.99  ground:                                 4
% 4.02/0.99  unary:                                  4
% 4.02/0.99  binary:                                 0
% 4.02/0.99  lits:                                   74
% 4.02/0.99  lits_eq:                                5
% 4.02/0.99  fd_pure:                                0
% 4.02/0.99  fd_pseudo:                              0
% 4.02/0.99  fd_cond:                                0
% 4.02/0.99  fd_pseudo_cond:                         4
% 4.02/0.99  ac_symbols:                             0
% 4.02/0.99  
% 4.02/0.99  ------ Propositional Solver
% 4.02/0.99  
% 4.02/0.99  prop_solver_calls:                      32
% 4.02/0.99  prop_fast_solver_calls:                 1275
% 4.02/0.99  smt_solver_calls:                       0
% 4.02/0.99  smt_fast_solver_calls:                  0
% 4.02/0.99  prop_num_of_clauses:                    3354
% 4.02/0.99  prop_preprocess_simplified:             10123
% 4.02/0.99  prop_fo_subsumed:                       46
% 4.02/0.99  prop_solver_time:                       0.
% 4.02/0.99  smt_solver_time:                        0.
% 4.02/0.99  smt_fast_solver_time:                   0.
% 4.02/0.99  prop_fast_solver_time:                  0.
% 4.02/0.99  prop_unsat_core_time:                   0.
% 4.02/0.99  
% 4.02/0.99  ------ QBF
% 4.02/0.99  
% 4.02/0.99  qbf_q_res:                              0
% 4.02/0.99  qbf_num_tautologies:                    0
% 4.02/0.99  qbf_prep_cycles:                        0
% 4.02/0.99  
% 4.02/0.99  ------ BMC1
% 4.02/0.99  
% 4.02/0.99  bmc1_current_bound:                     -1
% 4.02/0.99  bmc1_last_solved_bound:                 -1
% 4.02/0.99  bmc1_unsat_core_size:                   -1
% 4.02/0.99  bmc1_unsat_core_parents_size:           -1
% 4.02/0.99  bmc1_merge_next_fun:                    0
% 4.02/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation
% 4.02/0.99  
% 4.02/0.99  inst_num_of_clauses:                    1123
% 4.02/0.99  inst_num_in_passive:                    596
% 4.02/0.99  inst_num_in_active:                     488
% 4.02/0.99  inst_num_in_unprocessed:                39
% 4.02/0.99  inst_num_of_loops:                      502
% 4.02/0.99  inst_num_of_learning_restarts:          0
% 4.02/0.99  inst_num_moves_active_passive:          7
% 4.02/0.99  inst_lit_activity:                      0
% 4.02/0.99  inst_lit_activity_moves:                0
% 4.02/0.99  inst_num_tautologies:                   0
% 4.02/0.99  inst_num_prop_implied:                  0
% 4.02/0.99  inst_num_existing_simplified:           0
% 4.02/0.99  inst_num_eq_res_simplified:             0
% 4.02/0.99  inst_num_child_elim:                    0
% 4.02/0.99  inst_num_of_dismatching_blockings:      1545
% 4.02/0.99  inst_num_of_non_proper_insts:           2337
% 4.02/0.99  inst_num_of_duplicates:                 0
% 4.02/0.99  inst_inst_num_from_inst_to_res:         0
% 4.02/0.99  inst_dismatching_checking_time:         0.
% 4.02/0.99  
% 4.02/0.99  ------ Resolution
% 4.02/0.99  
% 4.02/0.99  res_num_of_clauses:                     0
% 4.02/0.99  res_num_in_passive:                     0
% 4.02/0.99  res_num_in_active:                      0
% 4.02/0.99  res_num_of_loops:                       96
% 4.02/0.99  res_forward_subset_subsumed:            74
% 4.02/0.99  res_backward_subset_subsumed:           2
% 4.02/0.99  res_forward_subsumed:                   0
% 4.02/0.99  res_backward_subsumed:                  0
% 4.02/0.99  res_forward_subsumption_resolution:     0
% 4.02/0.99  res_backward_subsumption_resolution:    0
% 4.02/0.99  res_clause_to_clause_subsumption:       631
% 4.02/0.99  res_orphan_elimination:                 0
% 4.02/0.99  res_tautology_del:                      129
% 4.02/0.99  res_num_eq_res_simplified:              0
% 4.02/0.99  res_num_sel_changes:                    0
% 4.02/0.99  res_moves_from_active_to_pass:          0
% 4.02/0.99  
% 4.02/0.99  ------ Superposition
% 4.02/0.99  
% 4.02/0.99  sup_time_total:                         0.
% 4.02/0.99  sup_time_generating:                    0.
% 4.02/0.99  sup_time_sim_full:                      0.
% 4.02/0.99  sup_time_sim_immed:                     0.
% 4.02/0.99  
% 4.02/0.99  sup_num_of_clauses:                     220
% 4.02/0.99  sup_num_in_active:                      100
% 4.02/0.99  sup_num_in_passive:                     120
% 4.02/0.99  sup_num_of_loops:                       100
% 4.02/0.99  sup_fw_superposition:                   120
% 4.02/0.99  sup_bw_superposition:                   88
% 4.02/0.99  sup_immediate_simplified:               68
% 4.02/0.99  sup_given_eliminated:                   0
% 4.02/0.99  comparisons_done:                       0
% 4.02/0.99  comparisons_avoided:                    0
% 4.02/0.99  
% 4.02/0.99  ------ Simplifications
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  sim_fw_subset_subsumed:                 0
% 4.02/0.99  sim_bw_subset_subsumed:                 0
% 4.02/0.99  sim_fw_subsumed:                        0
% 4.02/0.99  sim_bw_subsumed:                        0
% 4.02/0.99  sim_fw_subsumption_res:                 0
% 4.02/0.99  sim_bw_subsumption_res:                 0
% 4.02/0.99  sim_tautology_del:                      4
% 4.02/0.99  sim_eq_tautology_del:                   0
% 4.02/0.99  sim_eq_res_simp:                        0
% 4.02/0.99  sim_fw_demodulated:                     4
% 4.02/0.99  sim_bw_demodulated:                     0
% 4.02/0.99  sim_light_normalised:                   64
% 4.02/0.99  sim_joinable_taut:                      0
% 4.02/0.99  sim_joinable_simp:                      0
% 4.02/0.99  sim_ac_normalised:                      0
% 4.02/0.99  sim_smt_subsumption:                    0
% 4.02/0.99  
%------------------------------------------------------------------------------
