%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:15 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 436 expanded)
%              Number of clauses        :   72 ( 132 expanded)
%              Number of leaves         :   18 ( 111 expanded)
%              Depth                    :   21
%              Number of atoms          :  445 (1086 expanded)
%              Number of equality atoms :  165 ( 467 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
              & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
            | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
            | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
     => ( ( k3_xboole_0(X1,sK2) != k12_lattice3(k3_yellow_1(X0),X1,sK2)
          | k13_lattice3(k3_yellow_1(X0),X1,sK2) != k2_xboole_0(X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
              | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
            | k13_lattice3(k3_yellow_1(sK0),sK1,X2) != k2_xboole_0(sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
      | k13_lattice3(k3_yellow_1(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f44,f43])).

fof(f67,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f67,f53])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f63,f53])).

fof(f66,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f66,f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f59,f47,f53,f53])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X1,X2)) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f47,f47])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f48,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f24,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f57,plain,(
    ! [X0] :
      ( v2_lattice3(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f50,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f49,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X0] :
      ( v5_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f54,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f60,f53,f53])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X0] :
      ( v1_lattice3(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | k13_lattice3(k3_yellow_1(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(definition_unfolding,[],[f68,f47,f53,f53])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1178,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14,plain,
    ( k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1194,plain,
    ( m1_subset_1(sK2,k9_setfam_1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1178,c_13,c_14])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1177,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1191,plain,
    ( m1_subset_1(sK1,k9_setfam_1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1177,c_13,c_14])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | r2_hidden(k1_setfam_1(k2_tarski(X2,X0)),k9_setfam_1(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1181,plain,
    ( m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != iProver_top
    | r2_hidden(k1_setfam_1(k2_tarski(X2,X0)),k9_setfam_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1213,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(X1)) != iProver_top
    | r2_hidden(k1_setfam_1(k2_tarski(X2,X0)),k9_setfam_1(X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1181,c_13,c_14])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | v1_xboole_0(X1)
    | k11_lattice3(k2_yellow_1(X1),X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1179,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1251,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1179,c_13])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1184,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1257,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1251,c_1184])).

cnf(c_2546,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1257])).

cnf(c_2554,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0) = k1_setfam_1(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k9_setfam_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_2546])).

cnf(c_2662,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1194,c_2554])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( v2_lattice3(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_320,plain,
    ( v2_lattice3(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_321,plain,
    ( v2_lattice3(k3_lattice3(k1_lattice3(X0)))
    | ~ v10_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_3,plain,
    ( v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_325,plain,
    ( v2_lattice3(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_3,c_2])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2)
    | k3_lattice3(k1_lattice3(X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_325])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
    | k11_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) = k12_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_9,plain,
    ( v5_orders_2(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_290,plain,
    ( v5_orders_2(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_291,plain,
    ( v5_orders_2(k3_lattice3(k1_lattice3(X0)))
    | ~ v10_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_295,plain,
    ( v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_3,c_2])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
    | k11_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_342,c_295])).

cnf(c_1176,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != iProver_top
    | l1_orders_2(k3_lattice3(k1_lattice3(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_1230,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k12_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) != iProver_top
    | l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1176,c_14])).

cnf(c_1231,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k12_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1230,c_13])).

cnf(c_6,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1183,plain,
    ( l1_orders_2(k2_yellow_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1236,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k12_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1231,c_1183])).

cnf(c_1941,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0) = k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0)
    | m1_subset_1(X0,k9_setfam_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1236])).

cnf(c_1961,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1194,c_1941])).

cnf(c_2728,plain,
    ( k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2662,c_1961])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | r2_hidden(k2_xboole_0(X2,X0),k9_setfam_1(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1182,plain,
    ( m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != iProver_top
    | r2_hidden(k2_xboole_0(X2,X0),k9_setfam_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1206,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(X1)) != iProver_top
    | r2_hidden(k2_xboole_0(X2,X0),k9_setfam_1(X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1182,c_13,c_14])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k2_xboole_0(X2,X0),X1)
    | v1_xboole_0(X1)
    | k10_lattice3(k2_yellow_1(X1),X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1180,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r2_hidden(k2_xboole_0(X1,X2),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1240,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(k2_xboole_0(X1,X2),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1180,c_13])).

cnf(c_1246,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(k2_xboole_0(X1,X2),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1240,c_1184])).

cnf(c_2049,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_1246])).

cnf(c_2253,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k9_setfam_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_2049])).

cnf(c_2273,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1194,c_2253])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( v1_lattice3(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_305,plain,
    ( v1_lattice3(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_306,plain,
    ( v1_lattice3(k3_lattice3(k1_lattice3(X0)))
    | ~ v10_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_310,plain,
    ( v1_lattice3(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_3,c_2])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X0,X2) = k13_lattice3(X1,X0,X2)
    | k3_lattice3(k1_lattice3(X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_310])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
    | k10_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) = k13_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
    | k10_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_370,c_295])).

cnf(c_1175,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != iProver_top
    | l1_orders_2(k3_lattice3(k1_lattice3(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_1220,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k13_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) != iProver_top
    | l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1175,c_14])).

cnf(c_1221,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k13_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top
    | l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1220,c_13])).

cnf(c_1226,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k13_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1221,c_1183])).

cnf(c_1593,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0) = k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0)
    | m1_subset_1(X0,k9_setfam_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1226])).

cnf(c_1667,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1194,c_1593])).

cnf(c_2338,plain,
    ( k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2273,c_1667])).

cnf(c_17,negated_conjecture,
    ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1201,plain,
    ( k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_17,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2728,c_2338,c_1201])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 09:16:26 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.18/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/0.98  
% 2.18/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/0.98  
% 2.18/0.98  ------  iProver source info
% 2.18/0.98  
% 2.18/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.18/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/0.98  git: non_committed_changes: false
% 2.18/0.98  git: last_make_outside_of_git: false
% 2.18/0.98  
% 2.18/0.98  ------ 
% 2.18/0.98  
% 2.18/0.98  ------ Input Options
% 2.18/0.98  
% 2.18/0.98  --out_options                           all
% 2.18/0.98  --tptp_safe_out                         true
% 2.18/0.98  --problem_path                          ""
% 2.18/0.98  --include_path                          ""
% 2.18/0.98  --clausifier                            res/vclausify_rel
% 2.18/0.98  --clausifier_options                    --mode clausify
% 2.18/0.98  --stdin                                 false
% 2.18/0.98  --stats_out                             all
% 2.18/0.98  
% 2.18/0.98  ------ General Options
% 2.18/0.98  
% 2.18/0.98  --fof                                   false
% 2.18/0.98  --time_out_real                         305.
% 2.18/0.98  --time_out_virtual                      -1.
% 2.18/0.98  --symbol_type_check                     false
% 2.18/0.98  --clausify_out                          false
% 2.18/0.98  --sig_cnt_out                           false
% 2.18/0.98  --trig_cnt_out                          false
% 2.18/0.98  --trig_cnt_out_tolerance                1.
% 2.18/0.98  --trig_cnt_out_sk_spl                   false
% 2.18/0.98  --abstr_cl_out                          false
% 2.18/0.98  
% 2.18/0.98  ------ Global Options
% 2.18/0.98  
% 2.18/0.98  --schedule                              default
% 2.18/0.98  --add_important_lit                     false
% 2.18/0.98  --prop_solver_per_cl                    1000
% 2.18/0.98  --min_unsat_core                        false
% 2.18/0.98  --soft_assumptions                      false
% 2.18/0.98  --soft_lemma_size                       3
% 2.18/0.98  --prop_impl_unit_size                   0
% 2.18/0.98  --prop_impl_unit                        []
% 2.18/0.98  --share_sel_clauses                     true
% 2.18/0.98  --reset_solvers                         false
% 2.18/0.98  --bc_imp_inh                            [conj_cone]
% 2.18/0.98  --conj_cone_tolerance                   3.
% 2.18/0.98  --extra_neg_conj                        none
% 2.18/0.98  --large_theory_mode                     true
% 2.18/0.98  --prolific_symb_bound                   200
% 2.18/0.98  --lt_threshold                          2000
% 2.18/0.98  --clause_weak_htbl                      true
% 2.18/0.98  --gc_record_bc_elim                     false
% 2.18/0.98  
% 2.18/0.98  ------ Preprocessing Options
% 2.18/0.98  
% 2.18/0.98  --preprocessing_flag                    true
% 2.18/0.98  --time_out_prep_mult                    0.1
% 2.18/0.98  --splitting_mode                        input
% 2.18/0.98  --splitting_grd                         true
% 2.18/0.98  --splitting_cvd                         false
% 2.18/0.98  --splitting_cvd_svl                     false
% 2.18/0.98  --splitting_nvd                         32
% 2.18/0.98  --sub_typing                            true
% 2.18/0.98  --prep_gs_sim                           true
% 2.18/0.98  --prep_unflatten                        true
% 2.18/0.98  --prep_res_sim                          true
% 2.18/0.98  --prep_upred                            true
% 2.18/0.98  --prep_sem_filter                       exhaustive
% 2.18/0.98  --prep_sem_filter_out                   false
% 2.18/0.98  --pred_elim                             true
% 2.18/0.98  --res_sim_input                         true
% 2.18/0.98  --eq_ax_congr_red                       true
% 2.18/0.98  --pure_diseq_elim                       true
% 2.18/0.98  --brand_transform                       false
% 2.18/0.98  --non_eq_to_eq                          false
% 2.18/0.98  --prep_def_merge                        true
% 2.18/0.98  --prep_def_merge_prop_impl              false
% 2.18/0.98  --prep_def_merge_mbd                    true
% 2.18/0.98  --prep_def_merge_tr_red                 false
% 2.18/0.98  --prep_def_merge_tr_cl                  false
% 2.18/0.98  --smt_preprocessing                     true
% 2.18/0.98  --smt_ac_axioms                         fast
% 2.18/0.98  --preprocessed_out                      false
% 2.18/0.98  --preprocessed_stats                    false
% 2.18/0.98  
% 2.18/0.98  ------ Abstraction refinement Options
% 2.18/0.98  
% 2.18/0.98  --abstr_ref                             []
% 2.18/0.98  --abstr_ref_prep                        false
% 2.18/0.98  --abstr_ref_until_sat                   false
% 2.18/0.98  --abstr_ref_sig_restrict                funpre
% 2.18/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/0.98  --abstr_ref_under                       []
% 2.18/0.98  
% 2.18/0.98  ------ SAT Options
% 2.18/0.98  
% 2.18/0.98  --sat_mode                              false
% 2.18/0.98  --sat_fm_restart_options                ""
% 2.18/0.98  --sat_gr_def                            false
% 2.18/0.98  --sat_epr_types                         true
% 2.18/0.98  --sat_non_cyclic_types                  false
% 2.18/0.98  --sat_finite_models                     false
% 2.18/0.98  --sat_fm_lemmas                         false
% 2.18/0.98  --sat_fm_prep                           false
% 2.18/0.98  --sat_fm_uc_incr                        true
% 2.18/0.98  --sat_out_model                         small
% 2.18/0.98  --sat_out_clauses                       false
% 2.18/0.98  
% 2.18/0.98  ------ QBF Options
% 2.18/0.98  
% 2.18/0.98  --qbf_mode                              false
% 2.18/0.98  --qbf_elim_univ                         false
% 2.18/0.98  --qbf_dom_inst                          none
% 2.18/0.98  --qbf_dom_pre_inst                      false
% 2.18/0.98  --qbf_sk_in                             false
% 2.18/0.98  --qbf_pred_elim                         true
% 2.18/0.98  --qbf_split                             512
% 2.18/0.98  
% 2.18/0.98  ------ BMC1 Options
% 2.18/0.98  
% 2.18/0.98  --bmc1_incremental                      false
% 2.18/0.98  --bmc1_axioms                           reachable_all
% 2.18/0.98  --bmc1_min_bound                        0
% 2.18/0.98  --bmc1_max_bound                        -1
% 2.18/0.98  --bmc1_max_bound_default                -1
% 2.18/0.98  --bmc1_symbol_reachability              true
% 2.18/0.98  --bmc1_property_lemmas                  false
% 2.18/0.98  --bmc1_k_induction                      false
% 2.18/0.98  --bmc1_non_equiv_states                 false
% 2.18/0.98  --bmc1_deadlock                         false
% 2.18/0.98  --bmc1_ucm                              false
% 2.18/0.98  --bmc1_add_unsat_core                   none
% 2.18/0.98  --bmc1_unsat_core_children              false
% 2.18/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/0.98  --bmc1_out_stat                         full
% 2.18/0.98  --bmc1_ground_init                      false
% 2.18/0.98  --bmc1_pre_inst_next_state              false
% 2.18/0.98  --bmc1_pre_inst_state                   false
% 2.18/0.98  --bmc1_pre_inst_reach_state             false
% 2.18/0.98  --bmc1_out_unsat_core                   false
% 2.18/0.98  --bmc1_aig_witness_out                  false
% 2.18/0.98  --bmc1_verbose                          false
% 2.18/0.98  --bmc1_dump_clauses_tptp                false
% 2.18/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.18/0.98  --bmc1_dump_file                        -
% 2.18/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.18/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.18/0.98  --bmc1_ucm_extend_mode                  1
% 2.18/0.98  --bmc1_ucm_init_mode                    2
% 2.18/0.98  --bmc1_ucm_cone_mode                    none
% 2.18/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.18/0.98  --bmc1_ucm_relax_model                  4
% 2.18/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.18/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/0.98  --bmc1_ucm_layered_model                none
% 2.18/0.98  --bmc1_ucm_max_lemma_size               10
% 2.18/0.98  
% 2.18/0.98  ------ AIG Options
% 2.18/0.98  
% 2.18/0.98  --aig_mode                              false
% 2.18/0.98  
% 2.18/0.98  ------ Instantiation Options
% 2.18/0.98  
% 2.18/0.98  --instantiation_flag                    true
% 2.18/0.98  --inst_sos_flag                         false
% 2.18/0.98  --inst_sos_phase                        true
% 2.18/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/0.98  --inst_lit_sel_side                     num_symb
% 2.18/0.98  --inst_solver_per_active                1400
% 2.18/0.98  --inst_solver_calls_frac                1.
% 2.18/0.98  --inst_passive_queue_type               priority_queues
% 2.18/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/0.98  --inst_passive_queues_freq              [25;2]
% 2.18/0.98  --inst_dismatching                      true
% 2.18/0.98  --inst_eager_unprocessed_to_passive     true
% 2.18/0.98  --inst_prop_sim_given                   true
% 2.18/0.98  --inst_prop_sim_new                     false
% 2.18/0.98  --inst_subs_new                         false
% 2.18/0.98  --inst_eq_res_simp                      false
% 2.18/0.98  --inst_subs_given                       false
% 2.18/0.98  --inst_orphan_elimination               true
% 2.18/0.98  --inst_learning_loop_flag               true
% 2.18/0.98  --inst_learning_start                   3000
% 2.18/0.98  --inst_learning_factor                  2
% 2.18/0.98  --inst_start_prop_sim_after_learn       3
% 2.18/0.98  --inst_sel_renew                        solver
% 2.18/0.98  --inst_lit_activity_flag                true
% 2.18/0.98  --inst_restr_to_given                   false
% 2.18/0.98  --inst_activity_threshold               500
% 2.18/0.98  --inst_out_proof                        true
% 2.18/0.98  
% 2.18/0.98  ------ Resolution Options
% 2.18/0.98  
% 2.18/0.98  --resolution_flag                       true
% 2.18/0.98  --res_lit_sel                           adaptive
% 2.18/0.98  --res_lit_sel_side                      none
% 2.18/0.98  --res_ordering                          kbo
% 2.18/0.98  --res_to_prop_solver                    active
% 2.18/0.98  --res_prop_simpl_new                    false
% 2.18/0.98  --res_prop_simpl_given                  true
% 2.18/0.98  --res_passive_queue_type                priority_queues
% 2.18/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/0.98  --res_passive_queues_freq               [15;5]
% 2.18/0.98  --res_forward_subs                      full
% 2.18/0.98  --res_backward_subs                     full
% 2.18/0.98  --res_forward_subs_resolution           true
% 2.18/0.98  --res_backward_subs_resolution          true
% 2.18/0.98  --res_orphan_elimination                true
% 2.18/0.98  --res_time_limit                        2.
% 2.18/0.98  --res_out_proof                         true
% 2.18/0.98  
% 2.18/0.98  ------ Superposition Options
% 2.18/0.98  
% 2.18/0.98  --superposition_flag                    true
% 2.18/0.98  --sup_passive_queue_type                priority_queues
% 2.18/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.18/0.98  --demod_completeness_check              fast
% 2.18/0.98  --demod_use_ground                      true
% 2.18/0.98  --sup_to_prop_solver                    passive
% 2.18/0.98  --sup_prop_simpl_new                    true
% 2.18/0.98  --sup_prop_simpl_given                  true
% 2.18/0.98  --sup_fun_splitting                     false
% 2.18/0.98  --sup_smt_interval                      50000
% 2.18/0.98  
% 2.18/0.98  ------ Superposition Simplification Setup
% 2.18/0.98  
% 2.18/0.98  --sup_indices_passive                   []
% 2.18/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.98  --sup_full_bw                           [BwDemod]
% 2.18/0.98  --sup_immed_triv                        [TrivRules]
% 2.18/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.98  --sup_immed_bw_main                     []
% 2.18/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.98  
% 2.18/0.98  ------ Combination Options
% 2.18/0.98  
% 2.18/0.98  --comb_res_mult                         3
% 2.18/0.98  --comb_sup_mult                         2
% 2.18/0.98  --comb_inst_mult                        10
% 2.18/0.98  
% 2.18/0.98  ------ Debug Options
% 2.18/0.98  
% 2.18/0.98  --dbg_backtrace                         false
% 2.18/0.98  --dbg_dump_prop_clauses                 false
% 2.18/0.98  --dbg_dump_prop_clauses_file            -
% 2.18/0.98  --dbg_out_stat                          false
% 2.18/0.98  ------ Parsing...
% 2.18/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/0.98  
% 2.18/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.18/0.98  
% 2.18/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/0.98  
% 2.18/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/0.98  ------ Proving...
% 2.18/0.98  ------ Problem Properties 
% 2.18/0.98  
% 2.18/0.98  
% 2.18/0.98  clauses                                 13
% 2.18/0.98  conjectures                             3
% 2.18/0.98  EPR                                     1
% 2.18/0.98  Horn                                    11
% 2.18/0.98  unary                                   5
% 2.18/0.98  binary                                  2
% 2.18/0.98  lits                                    33
% 2.18/0.98  lits eq                                 8
% 2.18/0.98  fd_pure                                 0
% 2.18/0.98  fd_pseudo                               0
% 2.18/0.98  fd_cond                                 0
% 2.18/0.98  fd_pseudo_cond                          0
% 2.18/0.98  AC symbols                              0
% 2.18/0.98  
% 2.18/0.98  ------ Schedule dynamic 5 is on 
% 2.18/0.98  
% 2.18/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/0.98  
% 2.18/0.98  
% 2.18/0.98  ------ 
% 2.18/0.98  Current options:
% 2.18/0.98  ------ 
% 2.18/0.98  
% 2.18/0.98  ------ Input Options
% 2.18/0.98  
% 2.18/0.98  --out_options                           all
% 2.18/0.98  --tptp_safe_out                         true
% 2.18/0.98  --problem_path                          ""
% 2.18/0.98  --include_path                          ""
% 2.18/0.98  --clausifier                            res/vclausify_rel
% 2.18/0.98  --clausifier_options                    --mode clausify
% 2.18/0.98  --stdin                                 false
% 2.18/0.98  --stats_out                             all
% 2.18/0.98  
% 2.18/0.98  ------ General Options
% 2.18/0.98  
% 2.18/0.98  --fof                                   false
% 2.18/0.98  --time_out_real                         305.
% 2.18/0.98  --time_out_virtual                      -1.
% 2.18/0.98  --symbol_type_check                     false
% 2.18/0.98  --clausify_out                          false
% 2.18/0.98  --sig_cnt_out                           false
% 2.18/0.98  --trig_cnt_out                          false
% 2.18/0.98  --trig_cnt_out_tolerance                1.
% 2.18/0.98  --trig_cnt_out_sk_spl                   false
% 2.18/0.98  --abstr_cl_out                          false
% 2.18/0.98  
% 2.18/0.98  ------ Global Options
% 2.18/0.98  
% 2.18/0.98  --schedule                              default
% 2.18/0.98  --add_important_lit                     false
% 2.18/0.98  --prop_solver_per_cl                    1000
% 2.18/0.98  --min_unsat_core                        false
% 2.18/0.98  --soft_assumptions                      false
% 2.18/0.98  --soft_lemma_size                       3
% 2.18/0.98  --prop_impl_unit_size                   0
% 2.18/0.98  --prop_impl_unit                        []
% 2.18/0.98  --share_sel_clauses                     true
% 2.18/0.98  --reset_solvers                         false
% 2.18/0.98  --bc_imp_inh                            [conj_cone]
% 2.18/0.98  --conj_cone_tolerance                   3.
% 2.18/0.98  --extra_neg_conj                        none
% 2.18/0.98  --large_theory_mode                     true
% 2.18/0.98  --prolific_symb_bound                   200
% 2.18/0.98  --lt_threshold                          2000
% 2.18/0.98  --clause_weak_htbl                      true
% 2.18/0.98  --gc_record_bc_elim                     false
% 2.18/0.98  
% 2.18/0.98  ------ Preprocessing Options
% 2.18/0.98  
% 2.18/0.98  --preprocessing_flag                    true
% 2.18/0.98  --time_out_prep_mult                    0.1
% 2.18/0.98  --splitting_mode                        input
% 2.18/0.98  --splitting_grd                         true
% 2.18/0.98  --splitting_cvd                         false
% 2.18/0.98  --splitting_cvd_svl                     false
% 2.18/0.98  --splitting_nvd                         32
% 2.18/0.98  --sub_typing                            true
% 2.18/0.98  --prep_gs_sim                           true
% 2.18/0.98  --prep_unflatten                        true
% 2.18/0.98  --prep_res_sim                          true
% 2.18/0.98  --prep_upred                            true
% 2.18/0.98  --prep_sem_filter                       exhaustive
% 2.18/0.98  --prep_sem_filter_out                   false
% 2.18/0.98  --pred_elim                             true
% 2.18/0.98  --res_sim_input                         true
% 2.18/0.98  --eq_ax_congr_red                       true
% 2.18/0.98  --pure_diseq_elim                       true
% 2.18/0.98  --brand_transform                       false
% 2.18/0.98  --non_eq_to_eq                          false
% 2.18/0.98  --prep_def_merge                        true
% 2.18/0.98  --prep_def_merge_prop_impl              false
% 2.18/0.98  --prep_def_merge_mbd                    true
% 2.18/0.98  --prep_def_merge_tr_red                 false
% 2.18/0.98  --prep_def_merge_tr_cl                  false
% 2.18/0.98  --smt_preprocessing                     true
% 2.18/0.98  --smt_ac_axioms                         fast
% 2.18/0.98  --preprocessed_out                      false
% 2.18/0.98  --preprocessed_stats                    false
% 2.18/0.98  
% 2.18/0.98  ------ Abstraction refinement Options
% 2.18/0.98  
% 2.18/0.98  --abstr_ref                             []
% 2.18/0.98  --abstr_ref_prep                        false
% 2.18/0.98  --abstr_ref_until_sat                   false
% 2.18/0.98  --abstr_ref_sig_restrict                funpre
% 2.18/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/0.98  --abstr_ref_under                       []
% 2.18/0.98  
% 2.18/0.98  ------ SAT Options
% 2.18/0.98  
% 2.18/0.98  --sat_mode                              false
% 2.18/0.98  --sat_fm_restart_options                ""
% 2.18/0.98  --sat_gr_def                            false
% 2.18/0.98  --sat_epr_types                         true
% 2.18/0.98  --sat_non_cyclic_types                  false
% 2.18/0.98  --sat_finite_models                     false
% 2.18/0.98  --sat_fm_lemmas                         false
% 2.18/0.98  --sat_fm_prep                           false
% 2.18/0.98  --sat_fm_uc_incr                        true
% 2.18/0.98  --sat_out_model                         small
% 2.18/0.98  --sat_out_clauses                       false
% 2.18/0.98  
% 2.18/0.98  ------ QBF Options
% 2.18/0.98  
% 2.18/0.98  --qbf_mode                              false
% 2.18/0.98  --qbf_elim_univ                         false
% 2.18/0.98  --qbf_dom_inst                          none
% 2.18/0.98  --qbf_dom_pre_inst                      false
% 2.18/0.98  --qbf_sk_in                             false
% 2.18/0.98  --qbf_pred_elim                         true
% 2.18/0.98  --qbf_split                             512
% 2.18/0.98  
% 2.18/0.98  ------ BMC1 Options
% 2.18/0.98  
% 2.18/0.98  --bmc1_incremental                      false
% 2.18/0.98  --bmc1_axioms                           reachable_all
% 2.18/0.98  --bmc1_min_bound                        0
% 2.18/0.98  --bmc1_max_bound                        -1
% 2.18/0.98  --bmc1_max_bound_default                -1
% 2.18/0.98  --bmc1_symbol_reachability              true
% 2.18/0.98  --bmc1_property_lemmas                  false
% 2.18/0.98  --bmc1_k_induction                      false
% 2.18/0.98  --bmc1_non_equiv_states                 false
% 2.18/0.98  --bmc1_deadlock                         false
% 2.18/0.98  --bmc1_ucm                              false
% 2.18/0.98  --bmc1_add_unsat_core                   none
% 2.18/0.98  --bmc1_unsat_core_children              false
% 2.18/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/0.98  --bmc1_out_stat                         full
% 2.18/0.98  --bmc1_ground_init                      false
% 2.18/0.98  --bmc1_pre_inst_next_state              false
% 2.18/0.98  --bmc1_pre_inst_state                   false
% 2.18/0.98  --bmc1_pre_inst_reach_state             false
% 2.18/0.98  --bmc1_out_unsat_core                   false
% 2.18/0.98  --bmc1_aig_witness_out                  false
% 2.18/0.98  --bmc1_verbose                          false
% 2.18/0.98  --bmc1_dump_clauses_tptp                false
% 2.18/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.18/0.98  --bmc1_dump_file                        -
% 2.18/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.18/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.18/0.98  --bmc1_ucm_extend_mode                  1
% 2.18/0.98  --bmc1_ucm_init_mode                    2
% 2.18/0.98  --bmc1_ucm_cone_mode                    none
% 2.18/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.18/0.98  --bmc1_ucm_relax_model                  4
% 2.18/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.18/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/0.98  --bmc1_ucm_layered_model                none
% 2.18/0.98  --bmc1_ucm_max_lemma_size               10
% 2.18/0.98  
% 2.18/0.98  ------ AIG Options
% 2.18/0.98  
% 2.18/0.98  --aig_mode                              false
% 2.18/0.98  
% 2.18/0.98  ------ Instantiation Options
% 2.18/0.98  
% 2.18/0.98  --instantiation_flag                    true
% 2.18/0.98  --inst_sos_flag                         false
% 2.18/0.98  --inst_sos_phase                        true
% 2.18/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/0.98  --inst_lit_sel_side                     none
% 2.18/0.98  --inst_solver_per_active                1400
% 2.18/0.98  --inst_solver_calls_frac                1.
% 2.18/0.98  --inst_passive_queue_type               priority_queues
% 2.18/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/0.98  --inst_passive_queues_freq              [25;2]
% 2.18/0.98  --inst_dismatching                      true
% 2.18/0.98  --inst_eager_unprocessed_to_passive     true
% 2.18/0.98  --inst_prop_sim_given                   true
% 2.18/0.98  --inst_prop_sim_new                     false
% 2.18/0.98  --inst_subs_new                         false
% 2.18/0.98  --inst_eq_res_simp                      false
% 2.18/0.98  --inst_subs_given                       false
% 2.18/0.98  --inst_orphan_elimination               true
% 2.18/0.98  --inst_learning_loop_flag               true
% 2.18/0.98  --inst_learning_start                   3000
% 2.18/0.98  --inst_learning_factor                  2
% 2.18/0.98  --inst_start_prop_sim_after_learn       3
% 2.18/0.98  --inst_sel_renew                        solver
% 2.18/0.98  --inst_lit_activity_flag                true
% 2.18/0.98  --inst_restr_to_given                   false
% 2.18/0.98  --inst_activity_threshold               500
% 2.18/0.98  --inst_out_proof                        true
% 2.18/0.98  
% 2.18/0.98  ------ Resolution Options
% 2.18/0.98  
% 2.18/0.98  --resolution_flag                       false
% 2.18/0.98  --res_lit_sel                           adaptive
% 2.18/0.98  --res_lit_sel_side                      none
% 2.18/0.98  --res_ordering                          kbo
% 2.18/0.98  --res_to_prop_solver                    active
% 2.18/0.98  --res_prop_simpl_new                    false
% 2.18/0.98  --res_prop_simpl_given                  true
% 2.18/0.98  --res_passive_queue_type                priority_queues
% 2.18/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/0.98  --res_passive_queues_freq               [15;5]
% 2.18/0.98  --res_forward_subs                      full
% 2.18/0.98  --res_backward_subs                     full
% 2.18/0.98  --res_forward_subs_resolution           true
% 2.18/0.98  --res_backward_subs_resolution          true
% 2.18/0.98  --res_orphan_elimination                true
% 2.18/0.98  --res_time_limit                        2.
% 2.18/0.98  --res_out_proof                         true
% 2.18/0.98  
% 2.18/0.98  ------ Superposition Options
% 2.18/0.98  
% 2.18/0.98  --superposition_flag                    true
% 2.18/0.98  --sup_passive_queue_type                priority_queues
% 2.18/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.18/0.98  --demod_completeness_check              fast
% 2.18/0.98  --demod_use_ground                      true
% 2.18/0.98  --sup_to_prop_solver                    passive
% 2.18/0.98  --sup_prop_simpl_new                    true
% 2.18/0.98  --sup_prop_simpl_given                  true
% 2.18/0.98  --sup_fun_splitting                     false
% 2.18/0.98  --sup_smt_interval                      50000
% 2.18/0.98  
% 2.18/0.98  ------ Superposition Simplification Setup
% 2.18/0.98  
% 2.18/0.98  --sup_indices_passive                   []
% 2.18/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.98  --sup_full_bw                           [BwDemod]
% 2.18/0.98  --sup_immed_triv                        [TrivRules]
% 2.18/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.98  --sup_immed_bw_main                     []
% 2.18/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.98  
% 2.18/0.98  ------ Combination Options
% 2.18/0.98  
% 2.18/0.98  --comb_res_mult                         3
% 2.18/0.98  --comb_sup_mult                         2
% 2.18/0.98  --comb_inst_mult                        10
% 2.18/0.98  
% 2.18/0.98  ------ Debug Options
% 2.18/0.98  
% 2.18/0.98  --dbg_backtrace                         false
% 2.18/0.98  --dbg_dump_prop_clauses                 false
% 2.18/0.98  --dbg_dump_prop_clauses_file            -
% 2.18/0.98  --dbg_out_stat                          false
% 2.18/0.98  
% 2.18/0.98  
% 2.18/0.98  
% 2.18/0.98  
% 2.18/0.98  ------ Proving...
% 2.18/0.98  
% 2.18/0.98  
% 2.18/0.98  % SZS status Theorem for theBenchmark.p
% 2.18/0.98  
% 2.18/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/0.98  
% 2.18/0.98  fof(f17,conjecture,(
% 2.18/0.98    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2))))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f18,negated_conjecture,(
% 2.18/0.98    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2))))),
% 2.18/0.98    inference(negated_conjecture,[],[f17])).
% 2.18/0.98  
% 2.18/0.98  fof(f42,plain,(
% 2.18/0.98    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 2.18/0.98    inference(ennf_transformation,[],[f18])).
% 2.18/0.98  
% 2.18/0.98  fof(f44,plain,(
% 2.18/0.98    ( ! [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) => ((k3_xboole_0(X1,sK2) != k12_lattice3(k3_yellow_1(X0),X1,sK2) | k13_lattice3(k3_yellow_1(X0),X1,sK2) != k2_xboole_0(X1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(X0))))) )),
% 2.18/0.98    introduced(choice_axiom,[])).
% 2.18/0.98  
% 2.18/0.98  fof(f43,plain,(
% 2.18/0.98    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k13_lattice3(k3_yellow_1(sK0),sK1,X2) != k2_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 2.18/0.98    introduced(choice_axiom,[])).
% 2.18/0.98  
% 2.18/0.98  fof(f45,plain,(
% 2.18/0.98    ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k13_lattice3(k3_yellow_1(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 2.18/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f44,f43])).
% 2.18/0.98  
% 2.18/0.98  fof(f67,plain,(
% 2.18/0.98    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 2.18/0.98    inference(cnf_transformation,[],[f45])).
% 2.18/0.98  
% 2.18/0.98  fof(f8,axiom,(
% 2.18/0.98    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f53,plain,(
% 2.18/0.98    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.18/0.98    inference(cnf_transformation,[],[f8])).
% 2.18/0.98  
% 2.18/0.98  fof(f74,plain,(
% 2.18/0.98    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 2.18/0.98    inference(definition_unfolding,[],[f67,f53])).
% 2.18/0.98  
% 2.18/0.98  fof(f13,axiom,(
% 2.18/0.98    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f61,plain,(
% 2.18/0.98    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.18/0.98    inference(cnf_transformation,[],[f13])).
% 2.18/0.98  
% 2.18/0.98  fof(f14,axiom,(
% 2.18/0.98    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f63,plain,(
% 2.18/0.98    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 2.18/0.98    inference(cnf_transformation,[],[f14])).
% 2.18/0.98  
% 2.18/0.98  fof(f71,plain,(
% 2.18/0.98    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0))) )),
% 2.18/0.98    inference(definition_unfolding,[],[f63,f53])).
% 2.18/0.98  
% 2.18/0.98  fof(f66,plain,(
% 2.18/0.98    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 2.18/0.98    inference(cnf_transformation,[],[f45])).
% 2.18/0.98  
% 2.18/0.98  fof(f75,plain,(
% 2.18/0.98    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 2.18/0.98    inference(definition_unfolding,[],[f66,f53])).
% 2.18/0.98  
% 2.18/0.98  fof(f12,axiom,(
% 2.18/0.98    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)))))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f37,plain,(
% 2.18/0.98    ! [X0,X1] : (! [X2] : ((r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 2.18/0.98    inference(ennf_transformation,[],[f12])).
% 2.18/0.98  
% 2.18/0.98  fof(f59,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 2.18/0.98    inference(cnf_transformation,[],[f37])).
% 2.18/0.98  
% 2.18/0.98  fof(f2,axiom,(
% 2.18/0.98    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f47,plain,(
% 2.18/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f2])).
% 2.18/0.98  
% 2.18/0.98  fof(f70,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 2.18/0.98    inference(definition_unfolding,[],[f59,f47,f53,f53])).
% 2.18/0.98  
% 2.18/0.98  fof(f16,axiom,(
% 2.18/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k3_xboole_0(X1,X2),X0) => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f40,plain,(
% 2.18/0.98    ! [X0] : (! [X1] : (! [X2] : ((k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.18/0.98    inference(ennf_transformation,[],[f16])).
% 2.18/0.98  
% 2.18/0.98  fof(f41,plain,(
% 2.18/0.98    ! [X0] : (! [X1] : (! [X2] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.18/0.98    inference(flattening,[],[f40])).
% 2.18/0.98  
% 2.18/0.98  fof(f65,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f41])).
% 2.18/0.98  
% 2.18/0.98  fof(f72,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X1,X2)) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.18/0.98    inference(definition_unfolding,[],[f65,f47,f47])).
% 2.18/0.98  
% 2.18/0.98  fof(f1,axiom,(
% 2.18/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f19,plain,(
% 2.18/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.18/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 2.18/0.98  
% 2.18/0.98  fof(f30,plain,(
% 2.18/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.18/0.98    inference(ennf_transformation,[],[f19])).
% 2.18/0.98  
% 2.18/0.98  fof(f46,plain,(
% 2.18/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f30])).
% 2.18/0.98  
% 2.18/0.98  fof(f6,axiom,(
% 2.18/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f31,plain,(
% 2.18/0.98    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.18/0.98    inference(ennf_transformation,[],[f6])).
% 2.18/0.98  
% 2.18/0.98  fof(f32,plain,(
% 2.18/0.98    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.18/0.98    inference(flattening,[],[f31])).
% 2.18/0.98  
% 2.18/0.98  fof(f51,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f32])).
% 2.18/0.98  
% 2.18/0.98  fof(f3,axiom,(
% 2.18/0.98    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f29,plain,(
% 2.18/0.98    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 2.18/0.98    inference(pure_predicate_removal,[],[f3])).
% 2.18/0.98  
% 2.18/0.98  fof(f48,plain,(
% 2.18/0.98    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 2.18/0.98    inference(cnf_transformation,[],[f29])).
% 2.18/0.98  
% 2.18/0.98  fof(f10,axiom,(
% 2.18/0.98    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f20,plain,(
% 2.18/0.98    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 2.18/0.98    inference(pure_predicate_removal,[],[f10])).
% 2.18/0.98  
% 2.18/0.98  fof(f23,plain,(
% 2.18/0.98    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 2.18/0.98    inference(pure_predicate_removal,[],[f20])).
% 2.18/0.98  
% 2.18/0.98  fof(f24,plain,(
% 2.18/0.98    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))))),
% 2.18/0.98    inference(pure_predicate_removal,[],[f23])).
% 2.18/0.98  
% 2.18/0.98  fof(f35,plain,(
% 2.18/0.98    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.18/0.98    inference(ennf_transformation,[],[f24])).
% 2.18/0.98  
% 2.18/0.98  fof(f36,plain,(
% 2.18/0.98    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.18/0.98    inference(flattening,[],[f35])).
% 2.18/0.98  
% 2.18/0.98  fof(f57,plain,(
% 2.18/0.98    ( ! [X0] : (v2_lattice3(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f36])).
% 2.18/0.98  
% 2.18/0.98  fof(f5,axiom,(
% 2.18/0.98    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f28,plain,(
% 2.18/0.98    ! [X0] : v10_lattices(k1_lattice3(X0))),
% 2.18/0.98    inference(pure_predicate_removal,[],[f5])).
% 2.18/0.98  
% 2.18/0.98  fof(f50,plain,(
% 2.18/0.98    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 2.18/0.98    inference(cnf_transformation,[],[f28])).
% 2.18/0.98  
% 2.18/0.98  fof(f4,axiom,(
% 2.18/0.98    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f27,plain,(
% 2.18/0.98    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 2.18/0.98    inference(pure_predicate_removal,[],[f4])).
% 2.18/0.98  
% 2.18/0.98  fof(f49,plain,(
% 2.18/0.98    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 2.18/0.98    inference(cnf_transformation,[],[f27])).
% 2.18/0.98  
% 2.18/0.98  fof(f55,plain,(
% 2.18/0.98    ( ! [X0] : (v5_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f36])).
% 2.18/0.98  
% 2.18/0.98  fof(f9,axiom,(
% 2.18/0.98    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f25,plain,(
% 2.18/0.98    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.18/0.98    inference(pure_predicate_removal,[],[f9])).
% 2.18/0.98  
% 2.18/0.98  fof(f54,plain,(
% 2.18/0.98    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.18/0.98    inference(cnf_transformation,[],[f25])).
% 2.18/0.98  
% 2.18/0.98  fof(f60,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 2.18/0.98    inference(cnf_transformation,[],[f37])).
% 2.18/0.98  
% 2.18/0.98  fof(f69,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 2.18/0.98    inference(definition_unfolding,[],[f60,f53,f53])).
% 2.18/0.98  
% 2.18/0.98  fof(f15,axiom,(
% 2.18/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)))))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f38,plain,(
% 2.18/0.98    ! [X0] : (! [X1] : (! [X2] : ((k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.18/0.98    inference(ennf_transformation,[],[f15])).
% 2.18/0.98  
% 2.18/0.98  fof(f39,plain,(
% 2.18/0.98    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.18/0.98    inference(flattening,[],[f38])).
% 2.18/0.98  
% 2.18/0.98  fof(f64,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f39])).
% 2.18/0.98  
% 2.18/0.98  fof(f7,axiom,(
% 2.18/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 2.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.98  
% 2.18/0.98  fof(f33,plain,(
% 2.18/0.98    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.18/0.98    inference(ennf_transformation,[],[f7])).
% 2.18/0.98  
% 2.18/0.98  fof(f34,plain,(
% 2.18/0.98    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.18/0.98    inference(flattening,[],[f33])).
% 2.18/0.98  
% 2.18/0.98  fof(f52,plain,(
% 2.18/0.98    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f34])).
% 2.18/0.98  
% 2.18/0.98  fof(f56,plain,(
% 2.18/0.98    ( ! [X0] : (v1_lattice3(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.18/0.98    inference(cnf_transformation,[],[f36])).
% 2.18/0.98  
% 2.18/0.98  fof(f68,plain,(
% 2.18/0.98    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k13_lattice3(k3_yellow_1(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)),
% 2.18/0.98    inference(cnf_transformation,[],[f45])).
% 2.18/0.98  
% 2.18/0.98  fof(f73,plain,(
% 2.18/0.98    k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)),
% 2.18/0.98    inference(definition_unfolding,[],[f68,f47,f53,f53])).
% 2.18/0.98  
% 2.18/0.98  cnf(c_18,negated_conjecture,
% 2.18/0.98      ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 2.18/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1178,plain,
% 2.18/0.98      ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_13,plain,
% 2.18/0.98      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.18/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_14,plain,
% 2.18/0.98      ( k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0)) ),
% 2.18/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1194,plain,
% 2.18/0.98      ( m1_subset_1(sK2,k9_setfam_1(sK0)) = iProver_top ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_1178,c_13,c_14]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_19,negated_conjecture,
% 2.18/0.98      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 2.18/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1177,plain,
% 2.18/0.98      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1191,plain,
% 2.18/0.98      ( m1_subset_1(sK1,k9_setfam_1(sK0)) = iProver_top ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_1177,c_13,c_14]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_12,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | r2_hidden(k1_setfam_1(k2_tarski(X2,X0)),k9_setfam_1(X1)) ),
% 2.18/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1181,plain,
% 2.18/0.98      ( m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != iProver_top
% 2.18/0.98      | r2_hidden(k1_setfam_1(k2_tarski(X2,X0)),k9_setfam_1(X1)) = iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1213,plain,
% 2.18/0.98      ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,k9_setfam_1(X1)) != iProver_top
% 2.18/0.98      | r2_hidden(k1_setfam_1(k2_tarski(X2,X0)),k9_setfam_1(X1)) = iProver_top ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_1181,c_13,c_14]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_16,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.18/0.98      | ~ r2_hidden(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 2.18/0.98      | v1_xboole_0(X1)
% 2.18/0.98      | k11_lattice3(k2_yellow_1(X1),X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.18/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1179,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 2.18/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.18/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.18/0.98      | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) != iProver_top
% 2.18/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1251,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 2.18/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.18/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.18/0.98      | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) != iProver_top
% 2.18/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.18/0.98      inference(light_normalisation,[status(thm)],[c_1179,c_13]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_0,plain,
% 2.18/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.18/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1184,plain,
% 2.18/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.18/0.98      | v1_xboole_0(X1) != iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1257,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 2.18/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.18/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.18/0.98      | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) != iProver_top ),
% 2.18/0.98      inference(forward_subsumption_resolution,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_1251,c_1184]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2546,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 2.18/0.98      | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top
% 2.18/0.98      | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1213,c_1257]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2554,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0) = k1_setfam_1(k2_tarski(sK1,X0))
% 2.18/0.98      | m1_subset_1(X0,k9_setfam_1(sK0)) != iProver_top ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1191,c_2546]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2662,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1194,c_2554]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_4,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.18/0.98      | ~ v5_orders_2(X1)
% 2.18/0.98      | ~ v2_lattice3(X1)
% 2.18/0.98      | ~ l1_orders_2(X1)
% 2.18/0.98      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 2.18/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1,plain,
% 2.18/0.98      ( l3_lattices(k1_lattice3(X0)) ),
% 2.18/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_7,plain,
% 2.18/0.98      ( v2_lattice3(k3_lattice3(X0))
% 2.18/0.98      | ~ v10_lattices(X0)
% 2.18/0.98      | v2_struct_0(X0)
% 2.18/0.98      | ~ l3_lattices(X0) ),
% 2.18/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_320,plain,
% 2.18/0.98      ( v2_lattice3(k3_lattice3(X0))
% 2.18/0.98      | ~ v10_lattices(X0)
% 2.18/0.98      | v2_struct_0(X0)
% 2.18/0.98      | k1_lattice3(X1) != X0 ),
% 2.18/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_321,plain,
% 2.18/0.98      ( v2_lattice3(k3_lattice3(k1_lattice3(X0)))
% 2.18/0.98      | ~ v10_lattices(k1_lattice3(X0))
% 2.18/0.98      | v2_struct_0(k1_lattice3(X0)) ),
% 2.18/0.98      inference(unflattening,[status(thm)],[c_320]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_3,plain,
% 2.18/0.98      ( v10_lattices(k1_lattice3(X0)) ),
% 2.18/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2,plain,
% 2.18/0.98      ( ~ v2_struct_0(k1_lattice3(X0)) ),
% 2.18/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_325,plain,
% 2.18/0.98      ( v2_lattice3(k3_lattice3(k1_lattice3(X0))) ),
% 2.18/0.98      inference(global_propositional_subsumption,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_321,c_3,c_2]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_341,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.18/0.98      | ~ v5_orders_2(X1)
% 2.18/0.98      | ~ l1_orders_2(X1)
% 2.18/0.98      | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2)
% 2.18/0.98      | k3_lattice3(k1_lattice3(X3)) != X1 ),
% 2.18/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_325]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_342,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
% 2.18/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
% 2.18/0.98      | k11_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) = k12_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) ),
% 2.18/0.98      inference(unflattening,[status(thm)],[c_341]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_9,plain,
% 2.18/0.98      ( v5_orders_2(k3_lattice3(X0))
% 2.18/0.98      | ~ v10_lattices(X0)
% 2.18/0.98      | v2_struct_0(X0)
% 2.18/0.98      | ~ l3_lattices(X0) ),
% 2.18/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_290,plain,
% 2.18/0.98      ( v5_orders_2(k3_lattice3(X0))
% 2.18/0.98      | ~ v10_lattices(X0)
% 2.18/0.98      | v2_struct_0(X0)
% 2.18/0.98      | k1_lattice3(X1) != X0 ),
% 2.18/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_291,plain,
% 2.18/0.98      ( v5_orders_2(k3_lattice3(k1_lattice3(X0)))
% 2.18/0.98      | ~ v10_lattices(k1_lattice3(X0))
% 2.18/0.98      | v2_struct_0(k1_lattice3(X0)) ),
% 2.18/0.98      inference(unflattening,[status(thm)],[c_290]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_295,plain,
% 2.18/0.98      ( v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
% 2.18/0.98      inference(global_propositional_subsumption,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_291,c_3,c_2]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_356,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
% 2.18/0.98      | k11_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) ),
% 2.18/0.98      inference(forward_subsumption_resolution,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_342,c_295]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1176,plain,
% 2.18/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
% 2.18/0.98      | m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != iProver_top
% 2.18/0.98      | l1_orders_2(k3_lattice3(k1_lattice3(X0))) != iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1230,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k12_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
% 2.18/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) != iProver_top
% 2.18/0.98      | l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) != iProver_top ),
% 2.18/0.98      inference(light_normalisation,[status(thm)],[c_1176,c_14]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1231,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k12_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
% 2.18/0.98      | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top
% 2.18/0.98      | l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) != iProver_top ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_1230,c_13]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_6,plain,
% 2.18/0.98      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.18/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1183,plain,
% 2.18/0.98      ( l1_orders_2(k2_yellow_1(X0)) = iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1236,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k12_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
% 2.18/0.98      | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top ),
% 2.18/0.98      inference(forward_subsumption_resolution,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_1231,c_1183]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1941,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0) = k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0)
% 2.18/0.98      | m1_subset_1(X0,k9_setfam_1(sK0)) != iProver_top ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1191,c_1236]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1961,plain,
% 2.18/0.98      ( k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1194,c_1941]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2728,plain,
% 2.18/0.98      ( k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_2662,c_1961]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_11,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | r2_hidden(k2_xboole_0(X2,X0),k9_setfam_1(X1)) ),
% 2.18/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1182,plain,
% 2.18/0.98      ( m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != iProver_top
% 2.18/0.98      | r2_hidden(k2_xboole_0(X2,X0),k9_setfam_1(X1)) = iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1206,plain,
% 2.18/0.98      ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,k9_setfam_1(X1)) != iProver_top
% 2.18/0.98      | r2_hidden(k2_xboole_0(X2,X0),k9_setfam_1(X1)) = iProver_top ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_1182,c_13,c_14]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_15,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.18/0.98      | ~ r2_hidden(k2_xboole_0(X2,X0),X1)
% 2.18/0.98      | v1_xboole_0(X1)
% 2.18/0.98      | k10_lattice3(k2_yellow_1(X1),X2,X0) = k2_xboole_0(X2,X0) ),
% 2.18/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1180,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 2.18/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.18/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.18/0.98      | r2_hidden(k2_xboole_0(X1,X2),X0) != iProver_top
% 2.18/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1240,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 2.18/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.18/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.18/0.98      | r2_hidden(k2_xboole_0(X1,X2),X0) != iProver_top
% 2.18/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.18/0.98      inference(light_normalisation,[status(thm)],[c_1180,c_13]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1246,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
% 2.18/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.18/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.18/0.98      | r2_hidden(k2_xboole_0(X1,X2),X0) != iProver_top ),
% 2.18/0.98      inference(forward_subsumption_resolution,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_1240,c_1184]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2049,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k2_xboole_0(X1,X2)
% 2.18/0.98      | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top
% 2.18/0.98      | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1206,c_1246]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2253,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0) = k2_xboole_0(sK1,X0)
% 2.18/0.98      | m1_subset_1(X0,k9_setfam_1(sK0)) != iProver_top ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1191,c_2049]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2273,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1194,c_2253]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_5,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.18/0.98      | ~ v1_lattice3(X1)
% 2.18/0.98      | ~ v5_orders_2(X1)
% 2.18/0.98      | ~ l1_orders_2(X1)
% 2.18/0.98      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 2.18/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_8,plain,
% 2.18/0.98      ( v1_lattice3(k3_lattice3(X0))
% 2.18/0.98      | ~ v10_lattices(X0)
% 2.18/0.98      | v2_struct_0(X0)
% 2.18/0.98      | ~ l3_lattices(X0) ),
% 2.18/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_305,plain,
% 2.18/0.98      ( v1_lattice3(k3_lattice3(X0))
% 2.18/0.98      | ~ v10_lattices(X0)
% 2.18/0.98      | v2_struct_0(X0)
% 2.18/0.98      | k1_lattice3(X1) != X0 ),
% 2.18/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_306,plain,
% 2.18/0.98      ( v1_lattice3(k3_lattice3(k1_lattice3(X0)))
% 2.18/0.98      | ~ v10_lattices(k1_lattice3(X0))
% 2.18/0.98      | v2_struct_0(k1_lattice3(X0)) ),
% 2.18/0.98      inference(unflattening,[status(thm)],[c_305]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_310,plain,
% 2.18/0.98      ( v1_lattice3(k3_lattice3(k1_lattice3(X0))) ),
% 2.18/0.98      inference(global_propositional_subsumption,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_306,c_3,c_2]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_369,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.18/0.98      | ~ v5_orders_2(X1)
% 2.18/0.98      | ~ l1_orders_2(X1)
% 2.18/0.98      | k10_lattice3(X1,X0,X2) = k13_lattice3(X1,X0,X2)
% 2.18/0.98      | k3_lattice3(k1_lattice3(X3)) != X1 ),
% 2.18/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_310]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_370,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
% 2.18/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
% 2.18/0.98      | k10_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) = k13_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) ),
% 2.18/0.98      inference(unflattening,[status(thm)],[c_369]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_384,plain,
% 2.18/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.18/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
% 2.18/0.98      | k10_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) ),
% 2.18/0.98      inference(forward_subsumption_resolution,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_370,c_295]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1175,plain,
% 2.18/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X0)),X1,X2)
% 2.18/0.98      | m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != iProver_top
% 2.18/0.98      | l1_orders_2(k3_lattice3(k1_lattice3(X0))) != iProver_top ),
% 2.18/0.98      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1220,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k13_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
% 2.18/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) != iProver_top
% 2.18/0.98      | l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) != iProver_top ),
% 2.18/0.98      inference(light_normalisation,[status(thm)],[c_1175,c_14]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1221,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k13_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
% 2.18/0.98      | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top
% 2.18/0.98      | l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) != iProver_top ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_1220,c_13]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1226,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2) = k13_lattice3(k2_yellow_1(k9_setfam_1(X0)),X1,X2)
% 2.18/0.98      | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
% 2.18/0.98      | m1_subset_1(X2,k9_setfam_1(X0)) != iProver_top ),
% 2.18/0.98      inference(forward_subsumption_resolution,
% 2.18/0.98                [status(thm)],
% 2.18/0.98                [c_1221,c_1183]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1593,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0) = k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,X0)
% 2.18/0.98      | m1_subset_1(X0,k9_setfam_1(sK0)) != iProver_top ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1191,c_1226]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1667,plain,
% 2.18/0.98      ( k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
% 2.18/0.98      inference(superposition,[status(thm)],[c_1194,c_1593]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_2338,plain,
% 2.18/0.98      ( k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_2273,c_1667]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_17,negated_conjecture,
% 2.18/0.98      ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 2.18/0.98      | k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
% 2.18/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(c_1201,plain,
% 2.18/0.98      ( k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 2.18/0.98      | k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 2.18/0.98      inference(demodulation,[status(thm)],[c_17,c_14]) ).
% 2.18/0.98  
% 2.18/0.98  cnf(contradiction,plain,
% 2.18/0.98      ( $false ),
% 2.18/0.98      inference(minisat,[status(thm)],[c_2728,c_2338,c_1201]) ).
% 2.18/0.98  
% 2.18/0.98  
% 2.18/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/0.98  
% 2.18/0.98  ------                               Statistics
% 2.18/0.98  
% 2.18/0.98  ------ General
% 2.18/0.98  
% 2.18/0.98  abstr_ref_over_cycles:                  0
% 2.18/0.98  abstr_ref_under_cycles:                 0
% 2.18/0.98  gc_basic_clause_elim:                   0
% 2.18/0.98  forced_gc_time:                         0
% 2.18/0.98  parsing_time:                           0.011
% 2.18/0.98  unif_index_cands_time:                  0.
% 2.18/0.98  unif_index_add_time:                    0.
% 2.18/0.98  orderings_time:                         0.
% 2.18/0.98  out_proof_time:                         0.011
% 2.18/0.98  total_time:                             0.154
% 2.18/0.98  num_of_symbols:                         56
% 2.18/0.98  num_of_terms:                           2683
% 2.18/0.98  
% 2.18/0.98  ------ Preprocessing
% 2.18/0.98  
% 2.18/0.98  num_of_splits:                          0
% 2.18/0.98  num_of_split_atoms:                     0
% 2.18/0.98  num_of_reused_defs:                     0
% 2.18/0.98  num_eq_ax_congr_red:                    18
% 2.18/0.98  num_of_sem_filtered_clauses:            1
% 2.18/0.98  num_of_subtypes:                        0
% 2.18/0.98  monotx_restored_types:                  0
% 2.18/0.98  sat_num_of_epr_types:                   0
% 2.18/0.98  sat_num_of_non_cyclic_types:            0
% 2.18/0.98  sat_guarded_non_collapsed_types:        0
% 2.18/0.98  num_pure_diseq_elim:                    0
% 2.18/0.98  simp_replaced_by:                       0
% 2.18/0.98  res_preprocessed:                       92
% 2.18/0.98  prep_upred:                             0
% 2.18/0.98  prep_unflattend:                        23
% 2.18/0.98  smt_new_axioms:                         0
% 2.18/0.98  pred_elim_cands:                        4
% 2.18/0.98  pred_elim:                              6
% 2.18/0.98  pred_elim_cl:                           7
% 2.18/0.98  pred_elim_cycles:                       14
% 2.18/0.98  merged_defs:                            0
% 2.18/0.98  merged_defs_ncl:                        0
% 2.18/0.98  bin_hyper_res:                          0
% 2.18/0.98  prep_cycles:                            4
% 2.18/0.98  pred_elim_time:                         0.021
% 2.18/0.98  splitting_time:                         0.
% 2.18/0.98  sem_filter_time:                        0.
% 2.18/0.98  monotx_time:                            0.001
% 2.18/0.98  subtype_inf_time:                       0.
% 2.18/0.98  
% 2.18/0.98  ------ Problem properties
% 2.18/0.98  
% 2.18/0.98  clauses:                                13
% 2.18/0.98  conjectures:                            3
% 2.18/0.98  epr:                                    1
% 2.18/0.98  horn:                                   11
% 2.18/0.98  ground:                                 3
% 2.18/0.98  unary:                                  5
% 2.18/0.98  binary:                                 2
% 2.18/0.98  lits:                                   33
% 2.18/0.98  lits_eq:                                8
% 2.18/0.98  fd_pure:                                0
% 2.18/0.98  fd_pseudo:                              0
% 2.18/0.98  fd_cond:                                0
% 2.18/0.98  fd_pseudo_cond:                         0
% 2.18/0.98  ac_symbols:                             0
% 2.18/0.98  
% 2.18/0.98  ------ Propositional Solver
% 2.18/0.98  
% 2.18/0.98  prop_solver_calls:                      28
% 2.18/0.98  prop_fast_solver_calls:                 732
% 2.18/0.98  smt_solver_calls:                       0
% 2.18/0.98  smt_fast_solver_calls:                  0
% 2.18/0.98  prop_num_of_clauses:                    984
% 2.18/0.98  prop_preprocess_simplified:             3318
% 2.18/0.98  prop_fo_subsumed:                       15
% 2.18/0.98  prop_solver_time:                       0.
% 2.18/0.98  smt_solver_time:                        0.
% 2.18/0.98  smt_fast_solver_time:                   0.
% 2.18/0.98  prop_fast_solver_time:                  0.
% 2.18/0.98  prop_unsat_core_time:                   0.
% 2.18/0.98  
% 2.18/0.98  ------ QBF
% 2.18/0.98  
% 2.18/0.98  qbf_q_res:                              0
% 2.18/0.98  qbf_num_tautologies:                    0
% 2.18/0.98  qbf_prep_cycles:                        0
% 2.18/0.98  
% 2.18/0.98  ------ BMC1
% 2.18/0.98  
% 2.18/0.98  bmc1_current_bound:                     -1
% 2.18/0.98  bmc1_last_solved_bound:                 -1
% 2.18/0.98  bmc1_unsat_core_size:                   -1
% 2.18/0.98  bmc1_unsat_core_parents_size:           -1
% 2.18/0.98  bmc1_merge_next_fun:                    0
% 2.18/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.18/0.98  
% 2.18/0.98  ------ Instantiation
% 2.18/0.98  
% 2.18/0.98  inst_num_of_clauses:                    323
% 2.18/0.98  inst_num_in_passive:                    63
% 2.18/0.98  inst_num_in_active:                     190
% 2.18/0.98  inst_num_in_unprocessed:                71
% 2.18/0.98  inst_num_of_loops:                      200
% 2.18/0.98  inst_num_of_learning_restarts:          0
% 2.18/0.98  inst_num_moves_active_passive:          6
% 2.18/0.98  inst_lit_activity:                      0
% 2.18/0.98  inst_lit_activity_moves:                0
% 2.18/0.98  inst_num_tautologies:                   0
% 2.18/0.98  inst_num_prop_implied:                  0
% 2.18/0.98  inst_num_existing_simplified:           0
% 2.18/0.98  inst_num_eq_res_simplified:             0
% 2.18/0.98  inst_num_child_elim:                    0
% 2.18/0.98  inst_num_of_dismatching_blockings:      66
% 2.18/0.98  inst_num_of_non_proper_insts:           271
% 2.18/0.98  inst_num_of_duplicates:                 0
% 2.18/0.98  inst_inst_num_from_inst_to_res:         0
% 2.18/0.98  inst_dismatching_checking_time:         0.
% 2.18/0.98  
% 2.18/0.98  ------ Resolution
% 2.18/0.98  
% 2.18/0.98  res_num_of_clauses:                     0
% 2.18/0.98  res_num_in_passive:                     0
% 2.18/0.98  res_num_in_active:                      0
% 2.18/0.98  res_num_of_loops:                       96
% 2.18/0.98  res_forward_subset_subsumed:            44
% 2.18/0.98  res_backward_subset_subsumed:           4
% 2.18/0.98  res_forward_subsumed:                   0
% 2.18/0.98  res_backward_subsumed:                  0
% 2.18/0.98  res_forward_subsumption_resolution:     4
% 2.18/0.98  res_backward_subsumption_resolution:    0
% 2.18/0.98  res_clause_to_clause_subsumption:       96
% 2.18/0.98  res_orphan_elimination:                 0
% 2.18/0.98  res_tautology_del:                      38
% 2.18/0.98  res_num_eq_res_simplified:              0
% 2.18/0.98  res_num_sel_changes:                    0
% 2.18/0.98  res_moves_from_active_to_pass:          0
% 2.18/0.98  
% 2.18/0.98  ------ Superposition
% 2.18/0.98  
% 2.18/0.98  sup_time_total:                         0.
% 2.18/0.98  sup_time_generating:                    0.
% 2.18/0.98  sup_time_sim_full:                      0.
% 2.18/0.98  sup_time_sim_immed:                     0.
% 2.18/0.98  
% 2.18/0.98  sup_num_of_clauses:                     39
% 2.18/0.98  sup_num_in_active:                      32
% 2.18/0.98  sup_num_in_passive:                     7
% 2.18/0.98  sup_num_of_loops:                       38
% 2.18/0.98  sup_fw_superposition:                   26
% 2.18/0.98  sup_bw_superposition:                   2
% 2.18/0.98  sup_immediate_simplified:               0
% 2.18/0.98  sup_given_eliminated:                   0
% 2.18/0.98  comparisons_done:                       0
% 2.18/0.98  comparisons_avoided:                    0
% 2.18/0.98  
% 2.18/0.98  ------ Simplifications
% 2.18/0.98  
% 2.18/0.98  
% 2.18/0.98  sim_fw_subset_subsumed:                 0
% 2.18/0.98  sim_bw_subset_subsumed:                 0
% 2.18/0.98  sim_fw_subsumed:                        0
% 2.18/0.98  sim_bw_subsumed:                        0
% 2.18/0.98  sim_fw_subsumption_res:                 4
% 2.18/0.98  sim_bw_subsumption_res:                 0
% 2.18/0.98  sim_tautology_del:                      0
% 2.18/0.98  sim_eq_tautology_del:                   0
% 2.18/0.98  sim_eq_res_simp:                        0
% 2.18/0.98  sim_fw_demodulated:                     7
% 2.18/0.98  sim_bw_demodulated:                     6
% 2.18/0.98  sim_light_normalised:                   4
% 2.18/0.98  sim_joinable_taut:                      0
% 2.18/0.98  sim_joinable_simp:                      0
% 2.18/0.98  sim_ac_normalised:                      0
% 2.18/0.98  sim_smt_subsumption:                    0
% 2.18/0.98  
%------------------------------------------------------------------------------
