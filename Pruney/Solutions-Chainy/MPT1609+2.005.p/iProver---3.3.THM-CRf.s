%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:16 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 577 expanded)
%              Number of clauses        :  127 ( 222 expanded)
%              Number of leaves         :   24 ( 131 expanded)
%              Depth                    :   21
%              Number of atoms          :  590 (1658 expanded)
%              Number of equality atoms :  260 ( 559 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
              & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) != k3_xboole_0(X1,X2)
            | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) != k3_xboole_0(X1,X2)
            | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
     => ( ( k12_lattice3(k3_yellow_1(X0),X1,sK2) != k3_xboole_0(X1,sK2)
          | k13_lattice3(k3_yellow_1(X0),X1,sK2) != k2_xboole_0(X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) != k3_xboole_0(X1,X2)
              | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( k12_lattice3(k3_yellow_1(sK0),sK1,X2) != k3_xboole_0(sK1,X2)
            | k13_lattice3(k3_yellow_1(sK0),sK1,X2) != k2_xboole_0(sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k12_lattice3(k3_yellow_1(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2)
      | k13_lattice3(k3_yellow_1(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f42,f41])).

fof(f62,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f62,f51])).

fof(f63,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f63,f51])).

fof(f13,axiom,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0] : g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) = k3_lattice3(k1_lattice3(X0)) ),
    inference(definition_unfolding,[],[f59,f50,f51])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k11_lattice3(k2_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) = k3_xboole_0(X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f50,f50,f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f57,f51,f51])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f45,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f18,plain,(
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

fof(f21,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f22,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X0] :
      ( v2_lattice3(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f47,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f46,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0] :
      ( v5_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f52,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X0] :
      ( v1_lattice3(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f58,f51,f51])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) = k2_xboole_0(X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f60,f50,f50,f50])).

fof(f64,plain,
    ( k12_lattice3(k3_yellow_1(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2)
    | k13_lattice3(k3_yellow_1(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,
    ( k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k3_xboole_0(sK1,sK2)
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(definition_unfolding,[],[f64,f51,f51])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_953,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1194,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_954,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1193,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_13,plain,
    ( g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_958,plain,
    ( g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) = k3_lattice3(k1_lattice3(X0_57)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ r2_hidden(k3_xboole_0(X2,X0),X1)
    | v1_xboole_0(X1)
    | k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59))))
    | ~ m1_subset_1(X1_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59))))
    | ~ r2_hidden(k3_xboole_0(X1_53,X0_53),X0_59)
    | v1_xboole_0(X0_59)
    | k11_lattice3(g1_orders_2(X0_59,k1_yellow_1(X0_59)),X1_53,X0_53) = k3_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1192,plain,
    ( k11_lattice3(g1_orders_2(X0_59,k1_yellow_1(X0_59)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
    | m1_subset_1(X0_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59)))) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59)))) != iProver_top
    | r2_hidden(k3_xboole_0(X0_53,X1_53),X0_59) != iProver_top
    | v1_xboole_0(X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_962,plain,
    ( ~ r2_hidden(X0_58,X0_59)
    | ~ v1_xboole_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1187,plain,
    ( r2_hidden(X0_58,X0_59) != iProver_top
    | v1_xboole_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_1256,plain,
    ( k11_lattice3(g1_orders_2(X0_59,k1_yellow_1(X0_59)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59)))) != iProver_top
    | r2_hidden(k3_xboole_0(X0_53,X1_53),X0_59) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1192,c_1187])).

cnf(c_3178,plain,
    ( k11_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
    | m1_subset_1(X0_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))))) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | r2_hidden(k3_xboole_0(X0_53,X1_53),k9_setfam_1(X0_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_1256])).

cnf(c_3179,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | r2_hidden(k3_xboole_0(X0_53,X1_53),k9_setfam_1(X0_57)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3178,c_958])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | r2_hidden(k3_xboole_0(X2,X0),k9_setfam_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_959,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
    | ~ m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
    | r2_hidden(k3_xboole_0(X1_53,X0_53),k9_setfam_1(X0_57)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_998,plain,
    ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | r2_hidden(k3_xboole_0(X0_53,X1_53),k9_setfam_1(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_3287,plain,
    ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3179,c_998])).

cnf(c_3288,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3287])).

cnf(c_3296,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2) = k3_xboole_0(X0_53,sK2)
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_3288])).

cnf(c_3314,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1194,c_3296])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( v2_lattice3(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_318,plain,
    ( v2_lattice3(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_319,plain,
    ( v2_lattice3(k3_lattice3(k1_lattice3(X0)))
    | ~ v10_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_3,plain,
    ( v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_323,plain,
    ( v2_lattice3(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_3,c_2])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2)
    | k3_lattice3(k1_lattice3(X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_323])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
    | k11_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) = k12_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_9,plain,
    ( v5_orders_2(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_288,plain,
    ( v5_orders_2(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_289,plain,
    ( v5_orders_2(k3_lattice3(k1_lattice3(X0)))
    | ~ v10_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_293,plain,
    ( v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_3,c_2])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
    | k11_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_340,c_293])).

cnf(c_952,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
    | ~ m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X0_57)))
    | k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_1195,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_1010,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_6,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_961,plain,
    ( l1_orders_2(g1_orders_2(X0_59,k1_yellow_1(X0_59))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1188,plain,
    ( l1_orders_2(g1_orders_2(X0_59,k1_yellow_1(X0_59))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_961])).

cnf(c_1350,plain,
    ( l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) = iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_1188])).

cnf(c_1817,plain,
    ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1195,c_1010,c_1350])).

cnf(c_1818,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1817])).

cnf(c_1826,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2) = k12_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2)
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1818])).

cnf(c_1943,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1194,c_1826])).

cnf(c_3432,plain,
    ( k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3314,c_1943])).

cnf(c_968,plain,
    ( X0_58 != X1_58
    | X2_58 != X1_58
    | X2_58 = X0_58 ),
    theory(equality)).

cnf(c_1292,plain,
    ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != X0_58
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) != X0_58 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_2393,plain,
    ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2)
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_2394,plain,
    ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2393])).

cnf(c_1797,plain,
    ( X0_58 != X1_58
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != X1_58
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = X0_58 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_2020,plain,
    ( X0_58 != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = X0_58
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_2311,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8,plain,
    ( v1_lattice3(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_303,plain,
    ( v1_lattice3(k3_lattice3(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_304,plain,
    ( v1_lattice3(k3_lattice3(k1_lattice3(X0)))
    | ~ v10_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_308,plain,
    ( v1_lattice3(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_3,c_2])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X0,X2) = k13_lattice3(X1,X0,X2)
    | k3_lattice3(k1_lattice3(X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_308])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
    | k10_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) = k13_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
    | k10_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_368,c_293])).

cnf(c_951,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
    | ~ m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
    | ~ l1_orders_2(k3_lattice3(k1_lattice3(X0_57)))
    | k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_1196,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_1013,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_2147,plain,
    ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1196,c_1013,c_1350])).

cnf(c_2148,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2147])).

cnf(c_2156,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2)
    | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_2148])).

cnf(c_2167,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_1420,plain,
    ( X0_58 != X1_58
    | k2_xboole_0(X0_53,X1_53) != X1_58
    | k2_xboole_0(X0_53,X1_53) = X0_58 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_1778,plain,
    ( X0_58 != k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,X1_53)
    | k2_xboole_0(X0_53,X1_53) = X0_58
    | k2_xboole_0(X0_53,X1_53) != k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_1420])).

cnf(c_2045,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2) != k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_2046,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2)
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_976,plain,
    ( k10_lattice3(X0_55,X0_53,X1_53) = k10_lattice3(X1_55,X0_53,X1_53)
    | X0_55 != X1_55 ),
    theory(equality)).

cnf(c_1788,plain,
    ( k10_lattice3(X0_55,sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
    | X0_55 != g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_1810,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
    | k3_lattice3(k1_lattice3(X0_57)) != g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) ),
    inference(instantiation,[status(thm)],[c_1788])).

cnf(c_1811,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2)
    | k3_lattice3(k1_lattice3(sK0)) != g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_966,plain,
    ( X0_58 = X0_58 ),
    theory(equality)).

cnf(c_1795,plain,
    ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_1345,plain,
    ( X0_58 != X1_58
    | k2_xboole_0(sK1,sK2) != X1_58
    | k2_xboole_0(sK1,sK2) = X0_58 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_1388,plain,
    ( X0_58 != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) = X0_58
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_1545,plain,
    ( k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_1548,plain,
    ( k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | r2_hidden(k2_xboole_0(X2,X0),k9_setfam_1(X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_960,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
    | ~ m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
    | r2_hidden(k2_xboole_0(X1_53,X0_53),k9_setfam_1(X0_57)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1189,plain,
    ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
    | r2_hidden(k2_xboole_0(X0_53,X1_53),k9_setfam_1(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_1405,plain,
    ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top
    | r2_hidden(k2_xboole_0(X0_53,sK2),k9_setfam_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1189])).

cnf(c_1468,plain,
    ( r2_hidden(k2_xboole_0(sK2,sK2),k9_setfam_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1405])).

cnf(c_1530,plain,
    ( v1_xboole_0(k9_setfam_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1187])).

cnf(c_967,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_1334,plain,
    ( X0_55 != X1_55
    | X0_55 = g1_orders_2(X0_59,k1_yellow_1(X0_59))
    | g1_orders_2(X0_59,k1_yellow_1(X0_59)) != X1_55 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1392,plain,
    ( X0_55 = g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))
    | X0_55 != k3_lattice3(k1_lattice3(X0_57))
    | g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) != k3_lattice3(k1_lattice3(X0_57)) ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_1514,plain,
    ( g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) != k3_lattice3(k1_lattice3(X0_57))
    | k3_lattice3(k1_lattice3(X0_57)) = g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))
    | k3_lattice3(k1_lattice3(X0_57)) != k3_lattice3(k1_lattice3(X0_57)) ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_1516,plain,
    ( g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))) != k3_lattice3(k1_lattice3(sK0))
    | k3_lattice3(k1_lattice3(sK0)) = g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))
    | k3_lattice3(k1_lattice3(sK0)) != k3_lattice3(k1_lattice3(sK0)) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_973,plain,
    ( ~ m1_subset_1(X0_53,X0_54)
    | m1_subset_1(X0_53,X1_54)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_1299,plain,
    ( m1_subset_1(sK1,X0_54)
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | X0_54 != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_1382,plain,
    ( m1_subset_1(sK1,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | u1_struct_0(X0_55) != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_1435,plain,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_1436,plain,
    ( u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | m1_subset_1(sK1,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_965,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1426,plain,
    ( k3_lattice3(k1_lattice3(sK0)) = k3_lattice3(k1_lattice3(sK0)) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_972,plain,
    ( X0_55 != X1_55
    | u1_struct_0(X0_55) = u1_struct_0(X1_55) ),
    theory(equality)).

cnf(c_1338,plain,
    ( X0_55 != k3_lattice3(k1_lattice3(sK0))
    | u1_struct_0(X0_55) = u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_1423,plain,
    ( g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))) != k3_lattice3(k1_lattice3(sK0))
    | u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) = u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_1416,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top
    | r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_1389,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ r2_hidden(k2_xboole_0(X2,X0),X1)
    | v1_xboole_0(X1)
    | k10_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_957,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59))))
    | ~ m1_subset_1(X1_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59))))
    | ~ r2_hidden(k2_xboole_0(X1_53,X0_53),X0_59)
    | v1_xboole_0(X0_59)
    | k10_lattice3(g1_orders_2(X0_59,k1_yellow_1(X0_59)),X1_53,X0_53) = k2_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
    | ~ m1_subset_1(X1_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
    | ~ r2_hidden(k2_xboole_0(X1_53,X0_53),k9_setfam_1(X0_57))
    | v1_xboole_0(k9_setfam_1(X0_57))
    | k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X1_53,X0_53) = k2_xboole_0(X1_53,X0_53) ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_1368,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
    | ~ r2_hidden(k2_xboole_0(X0_53,sK2),k9_setfam_1(X0_57))
    | v1_xboole_0(k9_setfam_1(X0_57))
    | k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,sK2) = k2_xboole_0(X0_53,sK2) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_1378,plain,
    ( k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,sK2) = k2_xboole_0(X0_53,sK2)
    | m1_subset_1(X0_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))))) != iProver_top
    | r2_hidden(k2_xboole_0(X0_53,sK2),k9_setfam_1(X0_57)) != iProver_top
    | v1_xboole_0(k9_setfam_1(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1368])).

cnf(c_1380,plain,
    ( k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))) != iProver_top
    | r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) != iProver_top
    | v1_xboole_0(k9_setfam_1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1294,plain,
    ( m1_subset_1(sK2,X0_54)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | X0_54 != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_1337,plain,
    ( m1_subset_1(sK2,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | u1_struct_0(X0_55) != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_1367,plain,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_1370,plain,
    ( u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1367])).

cnf(c_1372,plain,
    ( u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_16,negated_conjecture,
    ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_955,negated_conjecture,
    ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1001,plain,
    ( g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))) = k3_lattice3(k1_lattice3(sK0)) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3432,c_2394,c_2311,c_2167,c_2046,c_1811,c_1795,c_1548,c_1530,c_1516,c_1436,c_1426,c_1423,c_1416,c_1389,c_1380,c_1372,c_955,c_1001,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:07:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.59/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/0.98  
% 1.59/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.59/0.98  
% 1.59/0.98  ------  iProver source info
% 1.59/0.98  
% 1.59/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.59/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.59/0.98  git: non_committed_changes: false
% 1.59/0.98  git: last_make_outside_of_git: false
% 1.59/0.98  
% 1.59/0.98  ------ 
% 1.59/0.98  
% 1.59/0.98  ------ Input Options
% 1.59/0.98  
% 1.59/0.98  --out_options                           all
% 1.59/0.98  --tptp_safe_out                         true
% 1.59/0.98  --problem_path                          ""
% 1.59/0.98  --include_path                          ""
% 1.59/0.98  --clausifier                            res/vclausify_rel
% 1.59/0.98  --clausifier_options                    --mode clausify
% 1.59/0.98  --stdin                                 false
% 1.59/0.98  --stats_out                             all
% 1.59/0.98  
% 1.59/0.98  ------ General Options
% 1.59/0.98  
% 1.59/0.98  --fof                                   false
% 1.59/0.98  --time_out_real                         305.
% 1.59/0.98  --time_out_virtual                      -1.
% 1.59/0.98  --symbol_type_check                     false
% 1.59/0.98  --clausify_out                          false
% 1.59/0.98  --sig_cnt_out                           false
% 1.59/0.98  --trig_cnt_out                          false
% 1.59/0.98  --trig_cnt_out_tolerance                1.
% 1.59/0.98  --trig_cnt_out_sk_spl                   false
% 1.59/0.98  --abstr_cl_out                          false
% 1.59/0.98  
% 1.59/0.98  ------ Global Options
% 1.59/0.98  
% 1.59/0.98  --schedule                              default
% 1.59/0.98  --add_important_lit                     false
% 1.59/0.98  --prop_solver_per_cl                    1000
% 1.59/0.98  --min_unsat_core                        false
% 1.59/0.98  --soft_assumptions                      false
% 1.59/0.98  --soft_lemma_size                       3
% 1.59/0.98  --prop_impl_unit_size                   0
% 1.59/0.98  --prop_impl_unit                        []
% 1.59/0.98  --share_sel_clauses                     true
% 1.59/0.98  --reset_solvers                         false
% 1.59/0.98  --bc_imp_inh                            [conj_cone]
% 1.59/0.98  --conj_cone_tolerance                   3.
% 1.59/0.98  --extra_neg_conj                        none
% 1.59/0.98  --large_theory_mode                     true
% 1.59/0.98  --prolific_symb_bound                   200
% 1.59/0.98  --lt_threshold                          2000
% 1.59/0.98  --clause_weak_htbl                      true
% 1.59/0.98  --gc_record_bc_elim                     false
% 1.59/0.98  
% 1.59/0.98  ------ Preprocessing Options
% 1.59/0.98  
% 1.59/0.98  --preprocessing_flag                    true
% 1.59/0.98  --time_out_prep_mult                    0.1
% 1.59/0.98  --splitting_mode                        input
% 1.59/0.98  --splitting_grd                         true
% 1.59/0.98  --splitting_cvd                         false
% 1.59/0.98  --splitting_cvd_svl                     false
% 1.59/0.98  --splitting_nvd                         32
% 1.59/0.98  --sub_typing                            true
% 1.59/0.98  --prep_gs_sim                           true
% 1.59/0.98  --prep_unflatten                        true
% 1.59/0.98  --prep_res_sim                          true
% 1.59/0.98  --prep_upred                            true
% 1.59/0.98  --prep_sem_filter                       exhaustive
% 1.59/0.98  --prep_sem_filter_out                   false
% 1.59/0.98  --pred_elim                             true
% 1.59/0.98  --res_sim_input                         true
% 1.59/0.98  --eq_ax_congr_red                       true
% 1.59/0.98  --pure_diseq_elim                       true
% 1.59/0.98  --brand_transform                       false
% 1.59/0.98  --non_eq_to_eq                          false
% 1.59/0.98  --prep_def_merge                        true
% 1.59/0.98  --prep_def_merge_prop_impl              false
% 1.59/0.98  --prep_def_merge_mbd                    true
% 1.59/0.98  --prep_def_merge_tr_red                 false
% 1.59/0.98  --prep_def_merge_tr_cl                  false
% 1.59/0.98  --smt_preprocessing                     true
% 1.59/0.98  --smt_ac_axioms                         fast
% 1.59/0.98  --preprocessed_out                      false
% 1.59/0.98  --preprocessed_stats                    false
% 1.59/0.98  
% 1.59/0.98  ------ Abstraction refinement Options
% 1.59/0.98  
% 1.59/0.98  --abstr_ref                             []
% 1.59/0.98  --abstr_ref_prep                        false
% 1.59/0.98  --abstr_ref_until_sat                   false
% 1.59/0.98  --abstr_ref_sig_restrict                funpre
% 1.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.59/0.98  --abstr_ref_under                       []
% 1.59/0.98  
% 1.59/0.98  ------ SAT Options
% 1.59/0.98  
% 1.59/0.98  --sat_mode                              false
% 1.59/0.98  --sat_fm_restart_options                ""
% 1.59/0.98  --sat_gr_def                            false
% 1.59/0.98  --sat_epr_types                         true
% 1.59/0.98  --sat_non_cyclic_types                  false
% 1.59/0.98  --sat_finite_models                     false
% 1.59/0.98  --sat_fm_lemmas                         false
% 1.59/0.98  --sat_fm_prep                           false
% 1.59/0.98  --sat_fm_uc_incr                        true
% 1.59/0.98  --sat_out_model                         small
% 1.59/0.98  --sat_out_clauses                       false
% 1.59/0.98  
% 1.59/0.98  ------ QBF Options
% 1.59/0.98  
% 1.59/0.98  --qbf_mode                              false
% 1.59/0.98  --qbf_elim_univ                         false
% 1.59/0.98  --qbf_dom_inst                          none
% 1.59/0.98  --qbf_dom_pre_inst                      false
% 1.59/0.98  --qbf_sk_in                             false
% 1.59/0.98  --qbf_pred_elim                         true
% 1.59/0.98  --qbf_split                             512
% 1.59/0.98  
% 1.59/0.98  ------ BMC1 Options
% 1.59/0.98  
% 1.59/0.98  --bmc1_incremental                      false
% 1.59/0.98  --bmc1_axioms                           reachable_all
% 1.59/0.98  --bmc1_min_bound                        0
% 1.59/0.98  --bmc1_max_bound                        -1
% 1.59/0.98  --bmc1_max_bound_default                -1
% 1.59/0.98  --bmc1_symbol_reachability              true
% 1.59/0.98  --bmc1_property_lemmas                  false
% 1.59/0.98  --bmc1_k_induction                      false
% 1.59/0.98  --bmc1_non_equiv_states                 false
% 1.59/0.98  --bmc1_deadlock                         false
% 1.59/0.98  --bmc1_ucm                              false
% 1.59/0.98  --bmc1_add_unsat_core                   none
% 1.59/0.98  --bmc1_unsat_core_children              false
% 1.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.59/0.98  --bmc1_out_stat                         full
% 1.59/0.98  --bmc1_ground_init                      false
% 1.59/0.98  --bmc1_pre_inst_next_state              false
% 1.59/0.98  --bmc1_pre_inst_state                   false
% 1.59/0.98  --bmc1_pre_inst_reach_state             false
% 1.59/0.98  --bmc1_out_unsat_core                   false
% 1.59/0.98  --bmc1_aig_witness_out                  false
% 1.59/0.98  --bmc1_verbose                          false
% 1.59/0.98  --bmc1_dump_clauses_tptp                false
% 1.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.59/0.98  --bmc1_dump_file                        -
% 1.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.59/0.98  --bmc1_ucm_extend_mode                  1
% 1.59/0.98  --bmc1_ucm_init_mode                    2
% 1.59/0.98  --bmc1_ucm_cone_mode                    none
% 1.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.59/0.98  --bmc1_ucm_relax_model                  4
% 1.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.59/0.98  --bmc1_ucm_layered_model                none
% 1.59/0.98  --bmc1_ucm_max_lemma_size               10
% 1.59/0.98  
% 1.59/0.98  ------ AIG Options
% 1.59/0.98  
% 1.59/0.98  --aig_mode                              false
% 1.59/0.98  
% 1.59/0.98  ------ Instantiation Options
% 1.59/0.98  
% 1.59/0.98  --instantiation_flag                    true
% 1.59/0.98  --inst_sos_flag                         false
% 1.59/0.98  --inst_sos_phase                        true
% 1.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.59/0.98  --inst_lit_sel_side                     num_symb
% 1.59/0.98  --inst_solver_per_active                1400
% 1.59/0.98  --inst_solver_calls_frac                1.
% 1.59/0.98  --inst_passive_queue_type               priority_queues
% 1.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.59/0.98  --inst_passive_queues_freq              [25;2]
% 1.59/0.98  --inst_dismatching                      true
% 1.59/0.98  --inst_eager_unprocessed_to_passive     true
% 1.59/0.98  --inst_prop_sim_given                   true
% 1.59/0.98  --inst_prop_sim_new                     false
% 1.59/0.98  --inst_subs_new                         false
% 1.59/0.98  --inst_eq_res_simp                      false
% 1.59/0.98  --inst_subs_given                       false
% 1.59/0.98  --inst_orphan_elimination               true
% 1.59/0.98  --inst_learning_loop_flag               true
% 1.59/0.98  --inst_learning_start                   3000
% 1.59/0.98  --inst_learning_factor                  2
% 1.59/0.98  --inst_start_prop_sim_after_learn       3
% 1.59/0.98  --inst_sel_renew                        solver
% 1.59/0.98  --inst_lit_activity_flag                true
% 1.59/0.98  --inst_restr_to_given                   false
% 1.59/0.98  --inst_activity_threshold               500
% 1.59/0.98  --inst_out_proof                        true
% 1.59/0.98  
% 1.59/0.98  ------ Resolution Options
% 1.59/0.98  
% 1.59/0.98  --resolution_flag                       true
% 1.59/0.98  --res_lit_sel                           adaptive
% 1.59/0.98  --res_lit_sel_side                      none
% 1.59/0.98  --res_ordering                          kbo
% 1.59/0.98  --res_to_prop_solver                    active
% 1.59/0.98  --res_prop_simpl_new                    false
% 1.59/0.98  --res_prop_simpl_given                  true
% 1.59/0.98  --res_passive_queue_type                priority_queues
% 1.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.59/0.98  --res_passive_queues_freq               [15;5]
% 1.59/0.98  --res_forward_subs                      full
% 1.59/0.98  --res_backward_subs                     full
% 1.59/0.98  --res_forward_subs_resolution           true
% 1.59/0.98  --res_backward_subs_resolution          true
% 1.59/0.98  --res_orphan_elimination                true
% 1.59/0.98  --res_time_limit                        2.
% 1.59/0.98  --res_out_proof                         true
% 1.59/0.98  
% 1.59/0.98  ------ Superposition Options
% 1.59/0.98  
% 1.59/0.98  --superposition_flag                    true
% 1.59/0.98  --sup_passive_queue_type                priority_queues
% 1.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.59/0.98  --demod_completeness_check              fast
% 1.59/0.98  --demod_use_ground                      true
% 1.59/0.98  --sup_to_prop_solver                    passive
% 1.59/0.98  --sup_prop_simpl_new                    true
% 1.59/0.98  --sup_prop_simpl_given                  true
% 1.59/0.98  --sup_fun_splitting                     false
% 1.59/0.98  --sup_smt_interval                      50000
% 1.59/0.98  
% 1.59/0.98  ------ Superposition Simplification Setup
% 1.59/0.98  
% 1.59/0.98  --sup_indices_passive                   []
% 1.59/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.98  --sup_full_bw                           [BwDemod]
% 1.59/0.98  --sup_immed_triv                        [TrivRules]
% 1.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.98  --sup_immed_bw_main                     []
% 1.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/0.98  
% 1.59/0.98  ------ Combination Options
% 1.59/0.98  
% 1.59/0.98  --comb_res_mult                         3
% 1.59/0.98  --comb_sup_mult                         2
% 1.59/0.98  --comb_inst_mult                        10
% 1.59/0.98  
% 1.59/0.98  ------ Debug Options
% 1.59/0.98  
% 1.59/0.98  --dbg_backtrace                         false
% 1.59/0.98  --dbg_dump_prop_clauses                 false
% 1.59/0.98  --dbg_dump_prop_clauses_file            -
% 1.59/0.98  --dbg_out_stat                          false
% 1.59/0.98  ------ Parsing...
% 1.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.59/0.98  
% 1.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.59/0.98  
% 1.59/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.59/0.98  
% 1.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.59/0.98  ------ Proving...
% 1.59/0.98  ------ Problem Properties 
% 1.59/0.98  
% 1.59/0.98  
% 1.59/0.98  clauses                                 12
% 1.59/0.98  conjectures                             3
% 1.59/0.98  EPR                                     1
% 1.59/0.98  Horn                                    10
% 1.59/0.98  unary                                   4
% 1.59/0.98  binary                                  2
% 1.59/0.98  lits                                    32
% 1.59/0.98  lits eq                                 7
% 1.59/0.98  fd_pure                                 0
% 1.59/0.98  fd_pseudo                               0
% 1.59/0.98  fd_cond                                 0
% 1.59/0.98  fd_pseudo_cond                          0
% 1.59/0.98  AC symbols                              0
% 1.59/0.98  
% 1.59/0.98  ------ Schedule dynamic 5 is on 
% 1.59/0.98  
% 1.59/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.59/0.98  
% 1.59/0.98  
% 1.59/0.98  ------ 
% 1.59/0.98  Current options:
% 1.59/0.98  ------ 
% 1.59/0.98  
% 1.59/0.98  ------ Input Options
% 1.59/0.98  
% 1.59/0.98  --out_options                           all
% 1.59/0.98  --tptp_safe_out                         true
% 1.59/0.98  --problem_path                          ""
% 1.59/0.98  --include_path                          ""
% 1.59/0.98  --clausifier                            res/vclausify_rel
% 1.59/0.98  --clausifier_options                    --mode clausify
% 1.59/0.98  --stdin                                 false
% 1.59/0.98  --stats_out                             all
% 1.59/0.98  
% 1.59/0.98  ------ General Options
% 1.59/0.98  
% 1.59/0.98  --fof                                   false
% 1.59/0.98  --time_out_real                         305.
% 1.59/0.98  --time_out_virtual                      -1.
% 1.59/0.98  --symbol_type_check                     false
% 1.59/0.98  --clausify_out                          false
% 1.59/0.98  --sig_cnt_out                           false
% 1.59/0.98  --trig_cnt_out                          false
% 1.59/0.98  --trig_cnt_out_tolerance                1.
% 1.59/0.98  --trig_cnt_out_sk_spl                   false
% 1.59/0.98  --abstr_cl_out                          false
% 1.59/0.98  
% 1.59/0.98  ------ Global Options
% 1.59/0.98  
% 1.59/0.98  --schedule                              default
% 1.59/0.98  --add_important_lit                     false
% 1.59/0.98  --prop_solver_per_cl                    1000
% 1.59/0.98  --min_unsat_core                        false
% 1.59/0.98  --soft_assumptions                      false
% 1.59/0.98  --soft_lemma_size                       3
% 1.59/0.98  --prop_impl_unit_size                   0
% 1.59/0.98  --prop_impl_unit                        []
% 1.59/0.98  --share_sel_clauses                     true
% 1.59/0.98  --reset_solvers                         false
% 1.59/0.98  --bc_imp_inh                            [conj_cone]
% 1.59/0.98  --conj_cone_tolerance                   3.
% 1.59/0.98  --extra_neg_conj                        none
% 1.59/0.98  --large_theory_mode                     true
% 1.59/0.98  --prolific_symb_bound                   200
% 1.59/0.98  --lt_threshold                          2000
% 1.59/0.98  --clause_weak_htbl                      true
% 1.59/0.98  --gc_record_bc_elim                     false
% 1.59/0.98  
% 1.59/0.98  ------ Preprocessing Options
% 1.59/0.98  
% 1.59/0.98  --preprocessing_flag                    true
% 1.59/0.98  --time_out_prep_mult                    0.1
% 1.59/0.98  --splitting_mode                        input
% 1.59/0.98  --splitting_grd                         true
% 1.59/0.98  --splitting_cvd                         false
% 1.59/0.98  --splitting_cvd_svl                     false
% 1.59/0.98  --splitting_nvd                         32
% 1.59/0.98  --sub_typing                            true
% 1.59/0.98  --prep_gs_sim                           true
% 1.59/0.98  --prep_unflatten                        true
% 1.59/0.98  --prep_res_sim                          true
% 1.59/0.98  --prep_upred                            true
% 1.59/0.98  --prep_sem_filter                       exhaustive
% 1.59/0.98  --prep_sem_filter_out                   false
% 1.59/0.98  --pred_elim                             true
% 1.59/0.98  --res_sim_input                         true
% 1.59/0.98  --eq_ax_congr_red                       true
% 1.59/0.98  --pure_diseq_elim                       true
% 1.59/0.98  --brand_transform                       false
% 1.59/0.98  --non_eq_to_eq                          false
% 1.59/0.98  --prep_def_merge                        true
% 1.59/0.98  --prep_def_merge_prop_impl              false
% 1.59/0.98  --prep_def_merge_mbd                    true
% 1.59/0.98  --prep_def_merge_tr_red                 false
% 1.59/0.98  --prep_def_merge_tr_cl                  false
% 1.59/0.98  --smt_preprocessing                     true
% 1.59/0.98  --smt_ac_axioms                         fast
% 1.59/0.98  --preprocessed_out                      false
% 1.59/0.98  --preprocessed_stats                    false
% 1.59/0.98  
% 1.59/0.98  ------ Abstraction refinement Options
% 1.59/0.98  
% 1.59/0.98  --abstr_ref                             []
% 1.59/0.98  --abstr_ref_prep                        false
% 1.59/0.98  --abstr_ref_until_sat                   false
% 1.59/0.98  --abstr_ref_sig_restrict                funpre
% 1.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.59/0.98  --abstr_ref_under                       []
% 1.59/0.98  
% 1.59/0.98  ------ SAT Options
% 1.59/0.98  
% 1.59/0.98  --sat_mode                              false
% 1.59/0.98  --sat_fm_restart_options                ""
% 1.59/0.98  --sat_gr_def                            false
% 1.59/0.98  --sat_epr_types                         true
% 1.59/0.98  --sat_non_cyclic_types                  false
% 1.59/0.98  --sat_finite_models                     false
% 1.59/0.98  --sat_fm_lemmas                         false
% 1.59/0.98  --sat_fm_prep                           false
% 1.59/0.98  --sat_fm_uc_incr                        true
% 1.59/0.98  --sat_out_model                         small
% 1.59/0.98  --sat_out_clauses                       false
% 1.59/0.98  
% 1.59/0.98  ------ QBF Options
% 1.59/0.98  
% 1.59/0.98  --qbf_mode                              false
% 1.59/0.98  --qbf_elim_univ                         false
% 1.59/0.98  --qbf_dom_inst                          none
% 1.59/0.98  --qbf_dom_pre_inst                      false
% 1.59/0.98  --qbf_sk_in                             false
% 1.59/0.98  --qbf_pred_elim                         true
% 1.59/0.98  --qbf_split                             512
% 1.59/0.98  
% 1.59/0.98  ------ BMC1 Options
% 1.59/0.98  
% 1.59/0.98  --bmc1_incremental                      false
% 1.59/0.98  --bmc1_axioms                           reachable_all
% 1.59/0.98  --bmc1_min_bound                        0
% 1.59/0.98  --bmc1_max_bound                        -1
% 1.59/0.98  --bmc1_max_bound_default                -1
% 1.59/0.98  --bmc1_symbol_reachability              true
% 1.59/0.98  --bmc1_property_lemmas                  false
% 1.59/0.98  --bmc1_k_induction                      false
% 1.59/0.98  --bmc1_non_equiv_states                 false
% 1.59/0.98  --bmc1_deadlock                         false
% 1.59/0.98  --bmc1_ucm                              false
% 1.59/0.98  --bmc1_add_unsat_core                   none
% 1.59/0.98  --bmc1_unsat_core_children              false
% 1.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.59/0.98  --bmc1_out_stat                         full
% 1.59/0.98  --bmc1_ground_init                      false
% 1.59/0.98  --bmc1_pre_inst_next_state              false
% 1.59/0.98  --bmc1_pre_inst_state                   false
% 1.59/0.98  --bmc1_pre_inst_reach_state             false
% 1.59/0.98  --bmc1_out_unsat_core                   false
% 1.59/0.98  --bmc1_aig_witness_out                  false
% 1.59/0.98  --bmc1_verbose                          false
% 1.59/0.98  --bmc1_dump_clauses_tptp                false
% 1.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.59/0.98  --bmc1_dump_file                        -
% 1.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.59/0.98  --bmc1_ucm_extend_mode                  1
% 1.59/0.98  --bmc1_ucm_init_mode                    2
% 1.59/0.98  --bmc1_ucm_cone_mode                    none
% 1.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.59/0.98  --bmc1_ucm_relax_model                  4
% 1.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.59/0.98  --bmc1_ucm_layered_model                none
% 1.59/0.98  --bmc1_ucm_max_lemma_size               10
% 1.59/0.98  
% 1.59/0.98  ------ AIG Options
% 1.59/0.98  
% 1.59/0.98  --aig_mode                              false
% 1.59/0.98  
% 1.59/0.98  ------ Instantiation Options
% 1.59/0.98  
% 1.59/0.98  --instantiation_flag                    true
% 1.59/0.98  --inst_sos_flag                         false
% 1.59/0.98  --inst_sos_phase                        true
% 1.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.59/0.98  --inst_lit_sel_side                     none
% 1.59/0.98  --inst_solver_per_active                1400
% 1.59/0.98  --inst_solver_calls_frac                1.
% 1.59/0.98  --inst_passive_queue_type               priority_queues
% 1.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.59/0.98  --inst_passive_queues_freq              [25;2]
% 1.59/0.98  --inst_dismatching                      true
% 1.59/0.98  --inst_eager_unprocessed_to_passive     true
% 1.59/0.98  --inst_prop_sim_given                   true
% 1.59/0.98  --inst_prop_sim_new                     false
% 1.59/0.98  --inst_subs_new                         false
% 1.59/0.98  --inst_eq_res_simp                      false
% 1.59/0.98  --inst_subs_given                       false
% 1.59/0.98  --inst_orphan_elimination               true
% 1.59/0.98  --inst_learning_loop_flag               true
% 1.59/0.98  --inst_learning_start                   3000
% 1.59/0.98  --inst_learning_factor                  2
% 1.59/0.98  --inst_start_prop_sim_after_learn       3
% 1.59/0.98  --inst_sel_renew                        solver
% 1.59/0.98  --inst_lit_activity_flag                true
% 1.59/0.98  --inst_restr_to_given                   false
% 1.59/0.98  --inst_activity_threshold               500
% 1.59/0.98  --inst_out_proof                        true
% 1.59/0.98  
% 1.59/0.98  ------ Resolution Options
% 1.59/0.98  
% 1.59/0.98  --resolution_flag                       false
% 1.59/0.98  --res_lit_sel                           adaptive
% 1.59/0.98  --res_lit_sel_side                      none
% 1.59/0.98  --res_ordering                          kbo
% 1.59/0.98  --res_to_prop_solver                    active
% 1.59/0.98  --res_prop_simpl_new                    false
% 1.59/0.98  --res_prop_simpl_given                  true
% 1.59/0.98  --res_passive_queue_type                priority_queues
% 1.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.59/0.98  --res_passive_queues_freq               [15;5]
% 1.59/0.98  --res_forward_subs                      full
% 1.59/0.98  --res_backward_subs                     full
% 1.59/0.98  --res_forward_subs_resolution           true
% 1.59/0.98  --res_backward_subs_resolution          true
% 1.59/0.98  --res_orphan_elimination                true
% 1.59/0.98  --res_time_limit                        2.
% 1.59/0.98  --res_out_proof                         true
% 1.59/0.98  
% 1.59/0.98  ------ Superposition Options
% 1.59/0.98  
% 1.59/0.98  --superposition_flag                    true
% 1.59/0.98  --sup_passive_queue_type                priority_queues
% 1.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.59/0.98  --demod_completeness_check              fast
% 1.59/0.98  --demod_use_ground                      true
% 1.59/0.98  --sup_to_prop_solver                    passive
% 1.59/0.98  --sup_prop_simpl_new                    true
% 1.59/0.98  --sup_prop_simpl_given                  true
% 1.59/0.98  --sup_fun_splitting                     false
% 1.59/0.98  --sup_smt_interval                      50000
% 1.59/0.98  
% 1.59/0.98  ------ Superposition Simplification Setup
% 1.59/0.98  
% 1.59/0.98  --sup_indices_passive                   []
% 1.59/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.98  --sup_full_bw                           [BwDemod]
% 1.59/0.98  --sup_immed_triv                        [TrivRules]
% 1.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.98  --sup_immed_bw_main                     []
% 1.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/0.98  
% 1.59/0.98  ------ Combination Options
% 1.59/0.98  
% 1.59/0.98  --comb_res_mult                         3
% 1.59/0.98  --comb_sup_mult                         2
% 1.59/0.98  --comb_inst_mult                        10
% 1.59/0.98  
% 1.59/0.98  ------ Debug Options
% 1.59/0.98  
% 1.59/0.98  --dbg_backtrace                         false
% 1.59/0.98  --dbg_dump_prop_clauses                 false
% 1.59/0.98  --dbg_dump_prop_clauses_file            -
% 1.59/0.98  --dbg_out_stat                          false
% 1.59/0.98  
% 1.59/0.98  
% 1.59/0.98  
% 1.59/0.98  
% 1.59/0.98  ------ Proving...
% 1.59/0.98  
% 1.59/0.98  
% 1.59/0.98  % SZS status Theorem for theBenchmark.p
% 1.59/0.98  
% 1.59/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.59/0.98  
% 1.59/0.98  fof(f16,conjecture,(
% 1.59/0.98    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2))))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f17,negated_conjecture,(
% 1.59/0.98    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2))))),
% 1.59/0.98    inference(negated_conjecture,[],[f16])).
% 1.59/0.98  
% 1.59/0.98  fof(f40,plain,(
% 1.59/0.98    ? [X0,X1] : (? [X2] : ((k12_lattice3(k3_yellow_1(X0),X1,X2) != k3_xboole_0(X1,X2) | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 1.59/0.98    inference(ennf_transformation,[],[f17])).
% 1.59/0.98  
% 1.59/0.98  fof(f42,plain,(
% 1.59/0.98    ( ! [X0,X1] : (? [X2] : ((k12_lattice3(k3_yellow_1(X0),X1,X2) != k3_xboole_0(X1,X2) | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) => ((k12_lattice3(k3_yellow_1(X0),X1,sK2) != k3_xboole_0(X1,sK2) | k13_lattice3(k3_yellow_1(X0),X1,sK2) != k2_xboole_0(X1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(X0))))) )),
% 1.59/0.98    introduced(choice_axiom,[])).
% 1.59/0.98  
% 1.59/0.98  fof(f41,plain,(
% 1.59/0.98    ? [X0,X1] : (? [X2] : ((k12_lattice3(k3_yellow_1(X0),X1,X2) != k3_xboole_0(X1,X2) | k13_lattice3(k3_yellow_1(X0),X1,X2) != k2_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((k12_lattice3(k3_yellow_1(sK0),sK1,X2) != k3_xboole_0(sK1,X2) | k13_lattice3(k3_yellow_1(sK0),sK1,X2) != k2_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 1.59/0.98    introduced(choice_axiom,[])).
% 1.59/0.98  
% 1.59/0.98  fof(f43,plain,(
% 1.59/0.98    ((k12_lattice3(k3_yellow_1(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2) | k13_lattice3(k3_yellow_1(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 1.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f42,f41])).
% 1.59/0.98  
% 1.59/0.98  fof(f62,plain,(
% 1.59/0.98    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 1.59/0.98    inference(cnf_transformation,[],[f43])).
% 1.59/0.98  
% 1.59/0.98  fof(f8,axiom,(
% 1.59/0.98    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f51,plain,(
% 1.59/0.98    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.59/0.98    inference(cnf_transformation,[],[f8])).
% 1.59/0.98  
% 1.59/0.98  fof(f74,plain,(
% 1.59/0.98    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 1.59/0.98    inference(definition_unfolding,[],[f62,f51])).
% 1.59/0.98  
% 1.59/0.98  fof(f63,plain,(
% 1.59/0.98    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 1.59/0.98    inference(cnf_transformation,[],[f43])).
% 1.59/0.98  
% 1.59/0.98  fof(f73,plain,(
% 1.59/0.98    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 1.59/0.98    inference(definition_unfolding,[],[f63,f51])).
% 1.59/0.98  
% 1.59/0.98  fof(f13,axiom,(
% 1.59/0.98    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0)),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f59,plain,(
% 1.59/0.98    ( ! [X0] : (k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f13])).
% 1.59/0.98  
% 1.59/0.98  fof(f7,axiom,(
% 1.59/0.98    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f50,plain,(
% 1.59/0.98    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 1.59/0.98    inference(cnf_transformation,[],[f7])).
% 1.59/0.98  
% 1.59/0.98  fof(f69,plain,(
% 1.59/0.98    ( ! [X0] : (g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) = k3_lattice3(k1_lattice3(X0))) )),
% 1.59/0.98    inference(definition_unfolding,[],[f59,f50,f51])).
% 1.59/0.98  
% 1.59/0.98  fof(f15,axiom,(
% 1.59/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k3_xboole_0(X1,X2),X0) => k11_lattice3(k2_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)))))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f38,plain,(
% 1.59/0.98    ! [X0] : (! [X1] : (! [X2] : ((k11_lattice3(k2_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.59/0.98    inference(ennf_transformation,[],[f15])).
% 1.59/0.98  
% 1.59/0.98  fof(f39,plain,(
% 1.59/0.98    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(k2_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.59/0.98    inference(flattening,[],[f38])).
% 1.59/0.98  
% 1.59/0.98  fof(f61,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (k11_lattice3(k2_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f39])).
% 1.59/0.98  
% 1.59/0.98  fof(f71,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) = k3_xboole_0(X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 1.59/0.98    inference(definition_unfolding,[],[f61,f50,f50,f50])).
% 1.59/0.98  
% 1.59/0.98  fof(f1,axiom,(
% 1.59/0.98    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f28,plain,(
% 1.59/0.98    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.59/0.98    inference(ennf_transformation,[],[f1])).
% 1.59/0.98  
% 1.59/0.98  fof(f44,plain,(
% 1.59/0.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f28])).
% 1.59/0.98  
% 1.59/0.98  fof(f12,axiom,(
% 1.59/0.98    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)))))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f35,plain,(
% 1.59/0.98    ! [X0,X1] : (! [X2] : ((r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 1.59/0.98    inference(ennf_transformation,[],[f12])).
% 1.59/0.98  
% 1.59/0.98  fof(f57,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 1.59/0.98    inference(cnf_transformation,[],[f35])).
% 1.59/0.98  
% 1.59/0.98  fof(f68,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 1.59/0.98    inference(definition_unfolding,[],[f57,f51,f51])).
% 1.59/0.98  
% 1.59/0.98  fof(f5,axiom,(
% 1.59/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f29,plain,(
% 1.59/0.98    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.59/0.98    inference(ennf_transformation,[],[f5])).
% 1.59/0.98  
% 1.59/0.98  fof(f30,plain,(
% 1.59/0.98    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 1.59/0.98    inference(flattening,[],[f29])).
% 1.59/0.98  
% 1.59/0.98  fof(f48,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f30])).
% 1.59/0.98  
% 1.59/0.98  fof(f2,axiom,(
% 1.59/0.98    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f26,plain,(
% 1.59/0.98    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 1.59/0.98    inference(pure_predicate_removal,[],[f2])).
% 1.59/0.98  
% 1.59/0.98  fof(f45,plain,(
% 1.59/0.98    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 1.59/0.98    inference(cnf_transformation,[],[f26])).
% 1.59/0.98  
% 1.59/0.98  fof(f10,axiom,(
% 1.59/0.98    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f18,plain,(
% 1.59/0.98    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 1.59/0.98    inference(pure_predicate_removal,[],[f10])).
% 1.59/0.98  
% 1.59/0.98  fof(f21,plain,(
% 1.59/0.98    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 1.59/0.98    inference(pure_predicate_removal,[],[f18])).
% 1.59/0.98  
% 1.59/0.98  fof(f22,plain,(
% 1.59/0.98    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))))),
% 1.59/0.98    inference(pure_predicate_removal,[],[f21])).
% 1.59/0.98  
% 1.59/0.98  fof(f33,plain,(
% 1.59/0.98    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.98    inference(ennf_transformation,[],[f22])).
% 1.59/0.98  
% 1.59/0.98  fof(f34,plain,(
% 1.59/0.98    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.98    inference(flattening,[],[f33])).
% 1.59/0.98  
% 1.59/0.98  fof(f55,plain,(
% 1.59/0.98    ( ! [X0] : (v2_lattice3(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f34])).
% 1.59/0.98  
% 1.59/0.98  fof(f4,axiom,(
% 1.59/0.98    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f25,plain,(
% 1.59/0.98    ! [X0] : v10_lattices(k1_lattice3(X0))),
% 1.59/0.98    inference(pure_predicate_removal,[],[f4])).
% 1.59/0.98  
% 1.59/0.98  fof(f47,plain,(
% 1.59/0.98    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 1.59/0.98    inference(cnf_transformation,[],[f25])).
% 1.59/0.98  
% 1.59/0.98  fof(f3,axiom,(
% 1.59/0.98    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f27,plain,(
% 1.59/0.98    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 1.59/0.98    inference(pure_predicate_removal,[],[f3])).
% 1.59/0.98  
% 1.59/0.98  fof(f46,plain,(
% 1.59/0.98    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 1.59/0.98    inference(cnf_transformation,[],[f27])).
% 1.59/0.98  
% 1.59/0.98  fof(f53,plain,(
% 1.59/0.98    ( ! [X0] : (v5_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f34])).
% 1.59/0.98  
% 1.59/0.98  fof(f9,axiom,(
% 1.59/0.98    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f23,plain,(
% 1.59/0.98    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.59/0.98    inference(pure_predicate_removal,[],[f9])).
% 1.59/0.98  
% 1.59/0.98  fof(f52,plain,(
% 1.59/0.98    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.59/0.98    inference(cnf_transformation,[],[f23])).
% 1.59/0.98  
% 1.59/0.98  fof(f65,plain,(
% 1.59/0.98    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 1.59/0.98    inference(definition_unfolding,[],[f52,f50])).
% 1.59/0.98  
% 1.59/0.98  fof(f6,axiom,(
% 1.59/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f31,plain,(
% 1.59/0.98    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.59/0.98    inference(ennf_transformation,[],[f6])).
% 1.59/0.98  
% 1.59/0.98  fof(f32,plain,(
% 1.59/0.98    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 1.59/0.98    inference(flattening,[],[f31])).
% 1.59/0.98  
% 1.59/0.98  fof(f49,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f32])).
% 1.59/0.98  
% 1.59/0.98  fof(f54,plain,(
% 1.59/0.98    ( ! [X0] : (v1_lattice3(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f34])).
% 1.59/0.98  
% 1.59/0.98  fof(f58,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 1.59/0.98    inference(cnf_transformation,[],[f35])).
% 1.59/0.98  
% 1.59/0.98  fof(f67,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 1.59/0.98    inference(definition_unfolding,[],[f58,f51,f51])).
% 1.59/0.98  
% 1.59/0.98  fof(f14,axiom,(
% 1.59/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)))))),
% 1.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/0.98  
% 1.59/0.98  fof(f36,plain,(
% 1.59/0.98    ! [X0] : (! [X1] : (! [X2] : ((k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.59/0.98    inference(ennf_transformation,[],[f14])).
% 1.59/0.98  
% 1.59/0.98  fof(f37,plain,(
% 1.59/0.98    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.59/0.98    inference(flattening,[],[f36])).
% 1.59/0.98  
% 1.59/0.98  fof(f60,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (k10_lattice3(k2_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.59/0.98    inference(cnf_transformation,[],[f37])).
% 1.59/0.98  
% 1.59/0.98  fof(f70,plain,(
% 1.59/0.98    ( ! [X2,X0,X1] : (k10_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) = k2_xboole_0(X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 1.59/0.98    inference(definition_unfolding,[],[f60,f50,f50,f50])).
% 1.59/0.98  
% 1.59/0.98  fof(f64,plain,(
% 1.59/0.98    k12_lattice3(k3_yellow_1(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2) | k13_lattice3(k3_yellow_1(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)),
% 1.59/0.98    inference(cnf_transformation,[],[f43])).
% 1.59/0.98  
% 1.59/0.98  fof(f72,plain,(
% 1.59/0.98    k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k3_xboole_0(sK1,sK2) | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)),
% 1.59/0.98    inference(definition_unfolding,[],[f64,f51,f51])).
% 1.59/0.98  
% 1.59/0.98  cnf(c_18,negated_conjecture,
% 1.59/0.98      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 1.59/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_953,negated_conjecture,
% 1.59/0.98      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1194,plain,
% 1.59/0.98      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_17,negated_conjecture,
% 1.59/0.98      ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 1.59/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_954,negated_conjecture,
% 1.59/0.98      ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1193,plain,
% 1.59/0.98      ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_13,plain,
% 1.59/0.98      ( g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) = k3_lattice3(k1_lattice3(X0)) ),
% 1.59/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_958,plain,
% 1.59/0.98      ( g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) = k3_lattice3(k1_lattice3(X0_57)) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_15,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 1.59/0.98      | ~ r2_hidden(k3_xboole_0(X2,X0),X1)
% 1.59/0.98      | v1_xboole_0(X1)
% 1.59/0.98      | k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0) = k3_xboole_0(X2,X0) ),
% 1.59/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_956,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59))))
% 1.59/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59))))
% 1.59/0.98      | ~ r2_hidden(k3_xboole_0(X1_53,X0_53),X0_59)
% 1.59/0.98      | v1_xboole_0(X0_59)
% 1.59/0.98      | k11_lattice3(g1_orders_2(X0_59,k1_yellow_1(X0_59)),X1_53,X0_53) = k3_xboole_0(X1_53,X0_53) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1192,plain,
% 1.59/0.98      ( k11_lattice3(g1_orders_2(X0_59,k1_yellow_1(X0_59)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59)))) != iProver_top
% 1.59/0.98      | r2_hidden(k3_xboole_0(X0_53,X1_53),X0_59) != iProver_top
% 1.59/0.98      | v1_xboole_0(X0_59) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_0,plain,
% 1.59/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.59/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_962,plain,
% 1.59/0.98      ( ~ r2_hidden(X0_58,X0_59) | ~ v1_xboole_0(X0_59) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1187,plain,
% 1.59/0.98      ( r2_hidden(X0_58,X0_59) != iProver_top
% 1.59/0.98      | v1_xboole_0(X0_59) != iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1256,plain,
% 1.59/0.98      ( k11_lattice3(g1_orders_2(X0_59,k1_yellow_1(X0_59)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59)))) != iProver_top
% 1.59/0.98      | r2_hidden(k3_xboole_0(X0_53,X1_53),X0_59) != iProver_top ),
% 1.59/0.98      inference(forward_subsumption_resolution,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_1192,c_1187]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_3178,plain,
% 1.59/0.98      ( k11_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))))) != iProver_top
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | r2_hidden(k3_xboole_0(X0_53,X1_53),k9_setfam_1(X0_57)) != iProver_top ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_958,c_1256]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_3179,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | r2_hidden(k3_xboole_0(X0_53,X1_53),k9_setfam_1(X0_57)) != iProver_top ),
% 1.59/0.98      inference(light_normalisation,[status(thm)],[c_3178,c_958]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_12,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | r2_hidden(k3_xboole_0(X2,X0),k9_setfam_1(X1)) ),
% 1.59/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_959,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
% 1.59/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
% 1.59/0.98      | r2_hidden(k3_xboole_0(X1_53,X0_53),k9_setfam_1(X0_57)) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_998,plain,
% 1.59/0.98      ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | r2_hidden(k3_xboole_0(X0_53,X1_53),k9_setfam_1(X0_57)) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_959]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_3287,plain,
% 1.59/0.98      ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53) ),
% 1.59/0.98      inference(global_propositional_subsumption,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_3179,c_998]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_3288,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top ),
% 1.59/0.98      inference(renaming,[status(thm)],[c_3287]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_3296,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2) = k3_xboole_0(X0_53,sK2)
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_1193,c_3288]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_3314,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_1194,c_3296]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_4,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.59/0.98      | ~ v5_orders_2(X1)
% 1.59/0.98      | ~ v2_lattice3(X1)
% 1.59/0.98      | ~ l1_orders_2(X1)
% 1.59/0.98      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 1.59/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1,plain,
% 1.59/0.98      ( l3_lattices(k1_lattice3(X0)) ),
% 1.59/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_7,plain,
% 1.59/0.98      ( v2_lattice3(k3_lattice3(X0))
% 1.59/0.98      | ~ v10_lattices(X0)
% 1.59/0.98      | v2_struct_0(X0)
% 1.59/0.98      | ~ l3_lattices(X0) ),
% 1.59/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_318,plain,
% 1.59/0.98      ( v2_lattice3(k3_lattice3(X0))
% 1.59/0.98      | ~ v10_lattices(X0)
% 1.59/0.98      | v2_struct_0(X0)
% 1.59/0.98      | k1_lattice3(X1) != X0 ),
% 1.59/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_319,plain,
% 1.59/0.98      ( v2_lattice3(k3_lattice3(k1_lattice3(X0)))
% 1.59/0.98      | ~ v10_lattices(k1_lattice3(X0))
% 1.59/0.98      | v2_struct_0(k1_lattice3(X0)) ),
% 1.59/0.98      inference(unflattening,[status(thm)],[c_318]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_3,plain,
% 1.59/0.98      ( v10_lattices(k1_lattice3(X0)) ),
% 1.59/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2,plain,
% 1.59/0.98      ( ~ v2_struct_0(k1_lattice3(X0)) ),
% 1.59/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_323,plain,
% 1.59/0.98      ( v2_lattice3(k3_lattice3(k1_lattice3(X0))) ),
% 1.59/0.98      inference(global_propositional_subsumption,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_319,c_3,c_2]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_339,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.59/0.98      | ~ v5_orders_2(X1)
% 1.59/0.98      | ~ l1_orders_2(X1)
% 1.59/0.98      | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2)
% 1.59/0.98      | k3_lattice3(k1_lattice3(X3)) != X1 ),
% 1.59/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_323]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_340,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.59/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.59/0.98      | k11_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) = k12_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) ),
% 1.59/0.98      inference(unflattening,[status(thm)],[c_339]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_9,plain,
% 1.59/0.98      ( v5_orders_2(k3_lattice3(X0))
% 1.59/0.98      | ~ v10_lattices(X0)
% 1.59/0.98      | v2_struct_0(X0)
% 1.59/0.98      | ~ l3_lattices(X0) ),
% 1.59/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_288,plain,
% 1.59/0.98      ( v5_orders_2(k3_lattice3(X0))
% 1.59/0.98      | ~ v10_lattices(X0)
% 1.59/0.98      | v2_struct_0(X0)
% 1.59/0.98      | k1_lattice3(X1) != X0 ),
% 1.59/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_289,plain,
% 1.59/0.98      ( v5_orders_2(k3_lattice3(k1_lattice3(X0)))
% 1.59/0.98      | ~ v10_lattices(k1_lattice3(X0))
% 1.59/0.98      | v2_struct_0(k1_lattice3(X0)) ),
% 1.59/0.98      inference(unflattening,[status(thm)],[c_288]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_293,plain,
% 1.59/0.98      ( v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
% 1.59/0.98      inference(global_propositional_subsumption,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_289,c_3,c_2]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_354,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.59/0.98      | k11_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) = k12_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) ),
% 1.59/0.98      inference(forward_subsumption_resolution,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_340,c_293]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_952,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
% 1.59/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
% 1.59/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X0_57)))
% 1.59/0.98      | k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_354]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1195,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) != iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1010,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) != iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_6,plain,
% 1.59/0.98      ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 1.59/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_961,plain,
% 1.59/0.98      ( l1_orders_2(g1_orders_2(X0_59,k1_yellow_1(X0_59))) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1188,plain,
% 1.59/0.98      ( l1_orders_2(g1_orders_2(X0_59,k1_yellow_1(X0_59))) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_961]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1350,plain,
% 1.59/0.98      ( l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) = iProver_top ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_958,c_1188]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1817,plain,
% 1.59/0.98      ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) ),
% 1.59/0.98      inference(global_propositional_subsumption,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_1195,c_1010,c_1350]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1818,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k12_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top ),
% 1.59/0.98      inference(renaming,[status(thm)],[c_1817]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1826,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2) = k12_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2)
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_1193,c_1818]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1943,plain,
% 1.59/0.98      ( k11_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_1194,c_1826]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_3432,plain,
% 1.59/0.98      ( k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
% 1.59/0.98      inference(demodulation,[status(thm)],[c_3314,c_1943]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_968,plain,
% 1.59/0.98      ( X0_58 != X1_58 | X2_58 != X1_58 | X2_58 = X0_58 ),
% 1.59/0.98      theory(equality) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1292,plain,
% 1.59/0.98      ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != X0_58
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != X0_58 ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_968]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2393,plain,
% 1.59/0.98      ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2)
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1292]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2394,plain,
% 1.59/0.98      ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_2393]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1797,plain,
% 1.59/0.98      ( X0_58 != X1_58
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != X1_58
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = X0_58 ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_968]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2020,plain,
% 1.59/0.98      ( X0_58 != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = X0_58
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1797]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2311,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
% 1.59/0.98      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_2020]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_5,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.59/0.98      | ~ v1_lattice3(X1)
% 1.59/0.98      | ~ v5_orders_2(X1)
% 1.59/0.98      | ~ l1_orders_2(X1)
% 1.59/0.98      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 1.59/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_8,plain,
% 1.59/0.98      ( v1_lattice3(k3_lattice3(X0))
% 1.59/0.98      | ~ v10_lattices(X0)
% 1.59/0.98      | v2_struct_0(X0)
% 1.59/0.98      | ~ l3_lattices(X0) ),
% 1.59/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_303,plain,
% 1.59/0.98      ( v1_lattice3(k3_lattice3(X0))
% 1.59/0.98      | ~ v10_lattices(X0)
% 1.59/0.98      | v2_struct_0(X0)
% 1.59/0.98      | k1_lattice3(X1) != X0 ),
% 1.59/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_304,plain,
% 1.59/0.98      ( v1_lattice3(k3_lattice3(k1_lattice3(X0)))
% 1.59/0.98      | ~ v10_lattices(k1_lattice3(X0))
% 1.59/0.98      | v2_struct_0(k1_lattice3(X0)) ),
% 1.59/0.98      inference(unflattening,[status(thm)],[c_303]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_308,plain,
% 1.59/0.98      ( v1_lattice3(k3_lattice3(k1_lattice3(X0))) ),
% 1.59/0.98      inference(global_propositional_subsumption,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_304,c_3,c_2]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_367,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.59/0.98      | ~ v5_orders_2(X1)
% 1.59/0.98      | ~ l1_orders_2(X1)
% 1.59/0.98      | k10_lattice3(X1,X0,X2) = k13_lattice3(X1,X0,X2)
% 1.59/0.98      | k3_lattice3(k1_lattice3(X3)) != X1 ),
% 1.59/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_308]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_368,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.59/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.59/0.98      | k10_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) = k13_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X0) ),
% 1.59/0.98      inference(unflattening,[status(thm)],[c_367]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_382,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.59/0.98      | k10_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) = k13_lattice3(k3_lattice3(k1_lattice3(X1)),X0,X2) ),
% 1.59/0.98      inference(forward_subsumption_resolution,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_368,c_293]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_951,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
% 1.59/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
% 1.59/0.98      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X0_57)))
% 1.59/0.98      | k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_382]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1196,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) != iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_951]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1013,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | l1_orders_2(k3_lattice3(k1_lattice3(X0_57))) != iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_951]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2147,plain,
% 1.59/0.98      ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) ),
% 1.59/0.98      inference(global_propositional_subsumption,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_1196,c_1013,c_1350]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2148,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53) = k13_lattice3(k3_lattice3(k1_lattice3(X0_57)),X0_53,X1_53)
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top ),
% 1.59/0.98      inference(renaming,[status(thm)],[c_2147]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2156,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),X0_53,sK2)
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_1193,c_2148]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2167,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
% 1.59/0.98      | m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_2156]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1420,plain,
% 1.59/0.98      ( X0_58 != X1_58
% 1.59/0.98      | k2_xboole_0(X0_53,X1_53) != X1_58
% 1.59/0.98      | k2_xboole_0(X0_53,X1_53) = X0_58 ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_968]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1778,plain,
% 1.59/0.98      ( X0_58 != k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,X1_53)
% 1.59/0.98      | k2_xboole_0(X0_53,X1_53) = X0_58
% 1.59/0.98      | k2_xboole_0(X0_53,X1_53) != k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,X1_53) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1420]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2045,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2) != k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1778]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_2046,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_2045]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_976,plain,
% 1.59/0.98      ( k10_lattice3(X0_55,X0_53,X1_53) = k10_lattice3(X1_55,X0_53,X1_53)
% 1.59/0.98      | X0_55 != X1_55 ),
% 1.59/0.98      theory(equality) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1788,plain,
% 1.59/0.98      ( k10_lattice3(X0_55,sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
% 1.59/0.98      | X0_55 != g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_976]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1810,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(X0_57)),sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
% 1.59/0.98      | k3_lattice3(k1_lattice3(X0_57)) != g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1788]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1811,plain,
% 1.59/0.98      ( k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2)
% 1.59/0.98      | k3_lattice3(k1_lattice3(sK0)) != g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1810]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_966,plain,( X0_58 = X0_58 ),theory(equality) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1795,plain,
% 1.59/0.98      ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_966]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1345,plain,
% 1.59/0.98      ( X0_58 != X1_58
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != X1_58
% 1.59/0.98      | k2_xboole_0(sK1,sK2) = X0_58 ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_968]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1388,plain,
% 1.59/0.98      ( X0_58 != k2_xboole_0(sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) = X0_58
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1345]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1545,plain,
% 1.59/0.98      ( k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1388]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1548,plain,
% 1.59/0.98      ( k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) = k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2)
% 1.59/0.98      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1545]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_11,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.59/0.98      | r2_hidden(k2_xboole_0(X2,X0),k9_setfam_1(X1)) ),
% 1.59/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_960,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
% 1.59/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57))))
% 1.59/0.98      | r2_hidden(k2_xboole_0(X1_53,X0_53),k9_setfam_1(X0_57)) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1189,plain,
% 1.59/0.98      ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | m1_subset_1(X1_53,u1_struct_0(k3_lattice3(k1_lattice3(X0_57)))) != iProver_top
% 1.59/0.98      | r2_hidden(k2_xboole_0(X0_53,X1_53),k9_setfam_1(X0_57)) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_960]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1405,plain,
% 1.59/0.98      ( m1_subset_1(X0_53,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top
% 1.59/0.98      | r2_hidden(k2_xboole_0(X0_53,sK2),k9_setfam_1(sK0)) = iProver_top ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_1193,c_1189]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1468,plain,
% 1.59/0.98      ( r2_hidden(k2_xboole_0(sK2,sK2),k9_setfam_1(sK0)) = iProver_top ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_1193,c_1405]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1530,plain,
% 1.59/0.98      ( v1_xboole_0(k9_setfam_1(sK0)) != iProver_top ),
% 1.59/0.98      inference(superposition,[status(thm)],[c_1468,c_1187]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_967,plain,
% 1.59/0.98      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 1.59/0.98      theory(equality) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1334,plain,
% 1.59/0.98      ( X0_55 != X1_55
% 1.59/0.98      | X0_55 = g1_orders_2(X0_59,k1_yellow_1(X0_59))
% 1.59/0.98      | g1_orders_2(X0_59,k1_yellow_1(X0_59)) != X1_55 ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_967]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1392,plain,
% 1.59/0.98      ( X0_55 = g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))
% 1.59/0.98      | X0_55 != k3_lattice3(k1_lattice3(X0_57))
% 1.59/0.98      | g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) != k3_lattice3(k1_lattice3(X0_57)) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1334]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1514,plain,
% 1.59/0.98      ( g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))) != k3_lattice3(k1_lattice3(X0_57))
% 1.59/0.98      | k3_lattice3(k1_lattice3(X0_57)) = g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))
% 1.59/0.98      | k3_lattice3(k1_lattice3(X0_57)) != k3_lattice3(k1_lattice3(X0_57)) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1392]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1516,plain,
% 1.59/0.98      ( g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))) != k3_lattice3(k1_lattice3(sK0))
% 1.59/0.98      | k3_lattice3(k1_lattice3(sK0)) = g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))
% 1.59/0.98      | k3_lattice3(k1_lattice3(sK0)) != k3_lattice3(k1_lattice3(sK0)) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1514]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_973,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,X0_54)
% 1.59/0.98      | m1_subset_1(X0_53,X1_54)
% 1.59/0.98      | X1_54 != X0_54 ),
% 1.59/0.98      theory(equality) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1299,plain,
% 1.59/0.98      ( m1_subset_1(sK1,X0_54)
% 1.59/0.98      | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.59/0.98      | X0_54 != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_973]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1382,plain,
% 1.59/0.98      ( m1_subset_1(sK1,u1_struct_0(X0_55))
% 1.59/0.98      | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.59/0.98      | u1_struct_0(X0_55) != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1299]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1435,plain,
% 1.59/0.98      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))))
% 1.59/0.98      | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.59/0.98      | u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1382]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1436,plain,
% 1.59/0.98      ( u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.59/0.98      | m1_subset_1(sK1,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))) = iProver_top
% 1.59/0.98      | m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1435]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_965,plain,( X0_55 = X0_55 ),theory(equality) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1426,plain,
% 1.59/0.98      ( k3_lattice3(k1_lattice3(sK0)) = k3_lattice3(k1_lattice3(sK0)) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_965]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_972,plain,
% 1.59/0.98      ( X0_55 != X1_55 | u1_struct_0(X0_55) = u1_struct_0(X1_55) ),
% 1.59/0.98      theory(equality) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1338,plain,
% 1.59/0.98      ( X0_55 != k3_lattice3(k1_lattice3(sK0))
% 1.59/0.98      | u1_struct_0(X0_55) = u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_972]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1423,plain,
% 1.59/0.98      ( g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))) != k3_lattice3(k1_lattice3(sK0))
% 1.59/0.98      | u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) = u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1338]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1416,plain,
% 1.59/0.98      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top
% 1.59/0.98      | r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) = iProver_top ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1405]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1389,plain,
% 1.59/0.98      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_966]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_14,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 1.59/0.98      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 1.59/0.98      | ~ r2_hidden(k2_xboole_0(X2,X0),X1)
% 1.59/0.98      | v1_xboole_0(X1)
% 1.59/0.98      | k10_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0) = k2_xboole_0(X2,X0) ),
% 1.59/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_957,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59))))
% 1.59/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(g1_orders_2(X0_59,k1_yellow_1(X0_59))))
% 1.59/0.98      | ~ r2_hidden(k2_xboole_0(X1_53,X0_53),X0_59)
% 1.59/0.98      | v1_xboole_0(X0_59)
% 1.59/0.98      | k10_lattice3(g1_orders_2(X0_59,k1_yellow_1(X0_59)),X1_53,X0_53) = k2_xboole_0(X1_53,X0_53) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1323,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
% 1.59/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
% 1.59/0.98      | ~ r2_hidden(k2_xboole_0(X1_53,X0_53),k9_setfam_1(X0_57))
% 1.59/0.98      | v1_xboole_0(k9_setfam_1(X0_57))
% 1.59/0.98      | k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X1_53,X0_53) = k2_xboole_0(X1_53,X0_53) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_957]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1368,plain,
% 1.59/0.98      ( ~ m1_subset_1(X0_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
% 1.59/0.98      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
% 1.59/0.98      | ~ r2_hidden(k2_xboole_0(X0_53,sK2),k9_setfam_1(X0_57))
% 1.59/0.98      | v1_xboole_0(k9_setfam_1(X0_57))
% 1.59/0.98      | k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,sK2) = k2_xboole_0(X0_53,sK2) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1323]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1378,plain,
% 1.59/0.98      ( k10_lattice3(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))),X0_53,sK2) = k2_xboole_0(X0_53,sK2)
% 1.59/0.98      | m1_subset_1(X0_53,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))))) != iProver_top
% 1.59/0.98      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))))) != iProver_top
% 1.59/0.98      | r2_hidden(k2_xboole_0(X0_53,sK2),k9_setfam_1(X0_57)) != iProver_top
% 1.59/0.98      | v1_xboole_0(k9_setfam_1(X0_57)) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1368]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1380,plain,
% 1.59/0.98      ( k10_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))),sK1,sK2) = k2_xboole_0(sK1,sK2)
% 1.59/0.98      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))) != iProver_top
% 1.59/0.98      | m1_subset_1(sK1,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))) != iProver_top
% 1.59/0.98      | r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) != iProver_top
% 1.59/0.98      | v1_xboole_0(k9_setfam_1(sK0)) = iProver_top ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1378]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1294,plain,
% 1.59/0.98      ( m1_subset_1(sK2,X0_54)
% 1.59/0.98      | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.59/0.98      | X0_54 != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_973]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1337,plain,
% 1.59/0.98      ( m1_subset_1(sK2,u1_struct_0(X0_55))
% 1.59/0.98      | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.59/0.98      | u1_struct_0(X0_55) != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1294]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1367,plain,
% 1.59/0.98      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))))
% 1.59/0.98      | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.59/0.98      | u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0))) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1337]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1370,plain,
% 1.59/0.98      ( u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.59/0.98      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(X0_57),k1_yellow_1(k9_setfam_1(X0_57))))) = iProver_top
% 1.59/0.98      | m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1367]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1372,plain,
% 1.59/0.98      ( u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.59/0.98      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))) = iProver_top
% 1.59/0.98      | m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != iProver_top ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_1370]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_16,negated_conjecture,
% 1.59/0.98      ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 1.59/0.98      | k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
% 1.59/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_955,negated_conjecture,
% 1.59/0.98      ( k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 1.59/0.98      | k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
% 1.59/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_1001,plain,
% 1.59/0.98      ( g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))) = k3_lattice3(k1_lattice3(sK0)) ),
% 1.59/0.98      inference(instantiation,[status(thm)],[c_958]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_20,plain,
% 1.59/0.98      ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(c_19,plain,
% 1.59/0.98      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
% 1.59/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.59/0.98  
% 1.59/0.98  cnf(contradiction,plain,
% 1.59/0.98      ( $false ),
% 1.59/0.98      inference(minisat,
% 1.59/0.98                [status(thm)],
% 1.59/0.98                [c_3432,c_2394,c_2311,c_2167,c_2046,c_1811,c_1795,c_1548,
% 1.59/0.98                 c_1530,c_1516,c_1436,c_1426,c_1423,c_1416,c_1389,c_1380,
% 1.59/0.98                 c_1372,c_955,c_1001,c_20,c_19]) ).
% 1.59/0.98  
% 1.59/0.98  
% 1.59/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.59/0.98  
% 1.59/0.98  ------                               Statistics
% 1.59/0.98  
% 1.59/0.98  ------ General
% 1.59/0.98  
% 1.59/0.98  abstr_ref_over_cycles:                  0
% 1.59/0.98  abstr_ref_under_cycles:                 0
% 1.59/0.98  gc_basic_clause_elim:                   0
% 1.59/0.98  forced_gc_time:                         0
% 1.59/0.98  parsing_time:                           0.011
% 1.59/0.98  unif_index_cands_time:                  0.
% 1.59/0.98  unif_index_add_time:                    0.
% 1.59/0.98  orderings_time:                         0.
% 1.59/0.98  out_proof_time:                         0.012
% 1.59/0.98  total_time:                             0.147
% 1.59/0.98  num_of_symbols:                         61
% 1.59/0.98  num_of_terms:                           2701
% 1.59/0.98  
% 1.59/0.98  ------ Preprocessing
% 1.59/0.98  
% 1.59/0.98  num_of_splits:                          0
% 1.59/0.98  num_of_split_atoms:                     0
% 1.59/0.98  num_of_reused_defs:                     0
% 1.59/0.98  num_eq_ax_congr_red:                    33
% 1.59/0.98  num_of_sem_filtered_clauses:            1
% 1.59/0.98  num_of_subtypes:                        8
% 1.59/0.98  monotx_restored_types:                  0
% 1.59/0.98  sat_num_of_epr_types:                   0
% 1.59/0.98  sat_num_of_non_cyclic_types:            0
% 1.59/0.98  sat_guarded_non_collapsed_types:        0
% 1.59/0.98  num_pure_diseq_elim:                    0
% 1.59/0.98  simp_replaced_by:                       0
% 1.59/0.98  res_preprocessed:                       82
% 1.59/0.98  prep_upred:                             0
% 1.59/0.98  prep_unflattend:                        23
% 1.59/0.98  smt_new_axioms:                         0
% 1.59/0.98  pred_elim_cands:                        4
% 1.59/0.98  pred_elim:                              6
% 1.59/0.98  pred_elim_cl:                           7
% 1.59/0.98  pred_elim_cycles:                       14
% 1.59/0.98  merged_defs:                            0
% 1.59/0.98  merged_defs_ncl:                        0
% 1.59/0.98  bin_hyper_res:                          0
% 1.59/0.98  prep_cycles:                            4
% 1.59/0.98  pred_elim_time:                         0.015
% 1.59/0.98  splitting_time:                         0.
% 1.59/0.98  sem_filter_time:                        0.
% 1.59/0.98  monotx_time:                            0.
% 1.59/0.98  subtype_inf_time:                       0.
% 1.59/0.98  
% 1.59/0.98  ------ Problem properties
% 1.59/0.98  
% 1.59/0.98  clauses:                                12
% 1.59/0.98  conjectures:                            3
% 1.59/0.98  epr:                                    1
% 1.59/0.98  horn:                                   10
% 1.59/0.98  ground:                                 3
% 1.59/0.98  unary:                                  4
% 1.59/0.98  binary:                                 2
% 1.59/0.98  lits:                                   32
% 1.59/0.98  lits_eq:                                7
% 1.59/0.98  fd_pure:                                0
% 1.59/0.98  fd_pseudo:                              0
% 1.59/0.98  fd_cond:                                0
% 1.59/0.98  fd_pseudo_cond:                         0
% 1.59/0.98  ac_symbols:                             0
% 1.59/0.98  
% 1.59/0.98  ------ Propositional Solver
% 1.59/0.98  
% 1.59/0.98  prop_solver_calls:                      32
% 1.59/0.98  prop_fast_solver_calls:                 669
% 1.59/0.98  smt_solver_calls:                       0
% 1.59/0.98  smt_fast_solver_calls:                  0
% 1.59/0.98  prop_num_of_clauses:                    1002
% 1.59/0.98  prop_preprocess_simplified:             3205
% 1.59/0.98  prop_fo_subsumed:                       14
% 1.59/0.98  prop_solver_time:                       0.
% 1.59/0.98  smt_solver_time:                        0.
% 1.59/0.98  smt_fast_solver_time:                   0.
% 1.59/0.98  prop_fast_solver_time:                  0.
% 1.59/0.98  prop_unsat_core_time:                   0.
% 1.59/0.98  
% 1.59/0.98  ------ QBF
% 1.59/0.98  
% 1.59/0.98  qbf_q_res:                              0
% 1.59/0.98  qbf_num_tautologies:                    0
% 1.59/0.98  qbf_prep_cycles:                        0
% 1.59/0.98  
% 1.59/0.98  ------ BMC1
% 1.59/0.98  
% 1.59/0.98  bmc1_current_bound:                     -1
% 1.59/0.98  bmc1_last_solved_bound:                 -1
% 1.59/0.98  bmc1_unsat_core_size:                   -1
% 1.59/0.98  bmc1_unsat_core_parents_size:           -1
% 1.59/0.98  bmc1_merge_next_fun:                    0
% 1.59/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.59/0.98  
% 1.59/0.98  ------ Instantiation
% 1.59/0.98  
% 1.59/0.98  inst_num_of_clauses:                    373
% 1.59/0.98  inst_num_in_passive:                    115
% 1.59/0.98  inst_num_in_active:                     235
% 1.59/0.98  inst_num_in_unprocessed:                23
% 1.59/0.98  inst_num_of_loops:                      260
% 1.59/0.98  inst_num_of_learning_restarts:          0
% 1.59/0.98  inst_num_moves_active_passive:          15
% 1.59/0.98  inst_lit_activity:                      0
% 1.59/0.98  inst_lit_activity_moves:                0
% 1.59/0.98  inst_num_tautologies:                   0
% 1.59/0.98  inst_num_prop_implied:                  0
% 1.59/0.98  inst_num_existing_simplified:           0
% 1.59/0.98  inst_num_eq_res_simplified:             0
% 1.59/0.98  inst_num_child_elim:                    0
% 1.59/0.98  inst_num_of_dismatching_blockings:      163
% 1.59/0.98  inst_num_of_non_proper_insts:           538
% 1.59/0.98  inst_num_of_duplicates:                 0
% 1.59/0.98  inst_inst_num_from_inst_to_res:         0
% 1.59/0.98  inst_dismatching_checking_time:         0.
% 1.59/0.98  
% 1.59/0.98  ------ Resolution
% 1.59/0.98  
% 1.59/0.98  res_num_of_clauses:                     0
% 1.59/0.98  res_num_in_passive:                     0
% 1.59/0.98  res_num_in_active:                      0
% 1.59/0.98  res_num_of_loops:                       86
% 1.59/0.98  res_forward_subset_subsumed:            142
% 1.59/0.98  res_backward_subset_subsumed:           2
% 1.59/0.98  res_forward_subsumed:                   0
% 1.59/0.98  res_backward_subsumed:                  0
% 1.59/0.98  res_forward_subsumption_resolution:     8
% 1.59/0.98  res_backward_subsumption_resolution:    0
% 1.59/0.98  res_clause_to_clause_subsumption:       73
% 1.59/0.98  res_orphan_elimination:                 0
% 1.59/0.98  res_tautology_del:                      118
% 1.59/0.98  res_num_eq_res_simplified:              0
% 1.59/0.98  res_num_sel_changes:                    0
% 1.59/0.98  res_moves_from_active_to_pass:          0
% 1.59/0.98  
% 1.59/0.98  ------ Superposition
% 1.59/0.98  
% 1.59/0.98  sup_time_total:                         0.
% 1.59/0.98  sup_time_generating:                    0.
% 1.59/0.98  sup_time_sim_full:                      0.
% 1.59/0.98  sup_time_sim_immed:                     0.
% 1.59/0.98  
% 1.59/0.98  sup_num_of_clauses:                     50
% 1.59/0.98  sup_num_in_active:                      44
% 1.59/0.98  sup_num_in_passive:                     6
% 1.59/0.98  sup_num_of_loops:                       51
% 1.59/0.98  sup_fw_superposition:                   36
% 1.59/0.98  sup_bw_superposition:                   9
% 1.59/0.98  sup_immediate_simplified:               2
% 1.59/0.98  sup_given_eliminated:                   0
% 1.59/0.98  comparisons_done:                       0
% 1.59/0.98  comparisons_avoided:                    0
% 1.59/0.98  
% 1.59/0.98  ------ Simplifications
% 1.59/0.98  
% 1.59/0.98  
% 1.59/0.98  sim_fw_subset_subsumed:                 0
% 1.59/0.98  sim_bw_subset_subsumed:                 0
% 1.59/0.98  sim_fw_subsumed:                        0
% 1.59/0.98  sim_bw_subsumed:                        0
% 1.59/0.98  sim_fw_subsumption_res:                 2
% 1.59/0.98  sim_bw_subsumption_res:                 0
% 1.59/0.98  sim_tautology_del:                      0
% 1.59/0.98  sim_eq_tautology_del:                   0
% 1.59/0.98  sim_eq_res_simp:                        1
% 1.59/0.98  sim_fw_demodulated:                     0
% 1.59/0.98  sim_bw_demodulated:                     7
% 1.59/0.98  sim_light_normalised:                   2
% 1.59/0.98  sim_joinable_taut:                      0
% 1.59/0.98  sim_joinable_simp:                      0
% 1.59/0.98  sim_ac_normalised:                      0
% 1.59/0.98  sim_smt_subsumption:                    0
% 1.59/0.98  
%------------------------------------------------------------------------------
