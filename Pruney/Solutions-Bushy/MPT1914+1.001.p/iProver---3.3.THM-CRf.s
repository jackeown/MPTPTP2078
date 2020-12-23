%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1914+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:52 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 128 expanded)
%              Number of clauses        :   31 (  51 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 ( 294 expanded)
%              Number of equality atoms :   65 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f24,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_8,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_420,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,plain,
    ( ~ l1_orders_2(X0)
    | v1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_101,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | k7_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_102,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(k7_lattice3(X0))
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_106,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_102,c_2])).

cnf(c_419,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_106])).

cnf(c_502,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = k7_lattice3(sK0) ),
    inference(superposition,[status(thm)],[c_420,c_419])).

cnf(c_1,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_425,plain,
    ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_676,plain,
    ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(sK0) ),
    inference(superposition,[status(thm)],[c_420,c_425])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_421,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_785,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_421])).

cnf(c_7,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_21,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_266,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_478,plain,
    ( u1_struct_0(k7_lattice3(sK0)) != X0
    | u1_struct_0(sK0) != X0
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_4,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_540,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)))))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_788,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_struct_0(k7_lattice3(sK0)) = X0
    | m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_421])).

cnf(c_823,plain,
    ( ~ m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)))))
    | g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_struct_0(k7_lattice3(sK0)) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_788])).

cnf(c_1157,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_785,c_8,c_7,c_21,c_478,c_540,c_823])).

cnf(c_1166,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_1157])).

cnf(c_545,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) = iProver_top
    | l1_orders_2(k7_lattice3(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_20,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(k7_lattice3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_22,plain,
    ( l1_orders_2(k7_lattice3(sK0)) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1166,c_545,c_22,c_9])).


%------------------------------------------------------------------------------
