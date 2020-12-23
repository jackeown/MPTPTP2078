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
% DateTime   : Thu Dec  3 12:18:59 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 761 expanded)
%              Number of clauses        :   85 ( 334 expanded)
%              Number of leaves         :    9 ( 139 expanded)
%              Depth                    :   19
%              Number of atoms          :  241 (1645 expanded)
%              Number of equality atoms :  164 ( 730 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,
    ( ? [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_438,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_434,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | l1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_440,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_613,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_440])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_435,plain,
    ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_769,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),k3_relset_1(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))))) = k7_lattice3(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_435])).

cnf(c_1401,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k3_relset_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) = k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(superposition,[status(thm)],[c_434,c_769])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_443,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_986,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | l1_orders_2(g1_orders_2(X1,k3_relset_1(X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_443,c_440])).

cnf(c_1747,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) != iProver_top
    | l1_orders_2(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_986])).

cnf(c_2163,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) != iProver_top
    | l1_orders_2(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_1747])).

cnf(c_11,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_516,plain,
    ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_517,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) != iProver_top
    | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_519,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
    | l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_2589,plain,
    ( l1_orders_2(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2163,c_11,c_21,c_519])).

cnf(c_2597,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),k3_relset_1(u1_struct_0(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),u1_struct_0(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),u1_orders_2(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) = k7_lattice3(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    inference(superposition,[status(thm)],[c_2589,c_435])).

cnf(c_768,plain,
    ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(sK0) ),
    inference(superposition,[status(thm)],[c_434,c_435])).

cnf(c_1615,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
    | l1_orders_2(k7_lattice3(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_986])).

cnf(c_1803,plain,
    ( l1_orders_2(k7_lattice3(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1615,c_11,c_21])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_441,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1809,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = k7_lattice3(sK0)
    | v1_orders_2(k7_lattice3(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_441])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_439,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_987,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_orders_2(g1_orders_2(X1,k3_relset_1(X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_443,c_439])).

cnf(c_1650,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
    | v1_orders_2(k7_lattice3(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_987])).

cnf(c_2255,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = k7_lattice3(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1809,c_11,c_21,c_1650])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_436,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1123,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_436])).

cnf(c_554,plain,
    ( m1_subset_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_555,plain,
    ( m1_subset_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_557,plain,
    ( m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_1124,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_436])).

cnf(c_1254,plain,
    ( u1_struct_0(sK0) = X0
    | g1_orders_2(X0,X1) != k7_lattice3(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1123,c_11,c_21,c_557,c_1124])).

cnf(c_1255,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = X0 ),
    inference(renaming,[status(thm)],[c_1254])).

cnf(c_2261,plain,
    ( u1_struct_0(k7_lattice3(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2255,c_1255])).

cnf(c_878,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_441])).

cnf(c_575,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
    | ~ v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_581,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top
    | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_614,plain,
    ( l1_orders_2(X0) != iProver_top
    | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_439])).

cnf(c_2224,plain,
    ( l1_orders_2(X0) != iProver_top
    | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_878,c_581,c_613,c_614])).

cnf(c_2225,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2224])).

cnf(c_2232,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(superposition,[status(thm)],[c_434,c_2225])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_437,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2617,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2232,c_437])).

cnf(c_20,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_518,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_2199,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2618,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1
    | m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2232,c_437])).

cnf(c_2665,plain,
    ( ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2618])).

cnf(c_3212,plain,
    ( u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2617,c_10,c_20,c_518,c_2199,c_2665])).

cnf(c_3213,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1 ),
    inference(renaming,[status(thm)],[c_3212])).

cnf(c_3221,plain,
    ( u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_orders_2(sK0) ),
    inference(equality_resolution,[status(thm)],[c_3213])).

cnf(c_2615,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2232,c_436])).

cnf(c_2616,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0
    | m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2232,c_436])).

cnf(c_2659,plain,
    ( ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2616])).

cnf(c_2901,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2615,c_10,c_20,c_518,c_2199,c_2659])).

cnf(c_2902,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0 ),
    inference(renaming,[status(thm)],[c_2901])).

cnf(c_2910,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_2902])).

cnf(c_4656,plain,
    ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) = k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(demodulation,[status(thm)],[c_2910,c_1401])).

cnf(c_5356,plain,
    ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(demodulation,[status(thm)],[c_3221,c_4656])).

cnf(c_5367,plain,
    ( k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5356,c_768])).

cnf(c_1125,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = X0
    | g1_orders_2(X1,X0) != k7_lattice3(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_437])).

cnf(c_1126,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = X0
    | g1_orders_2(X1,X0) != k7_lattice3(sK0)
    | m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_437])).

cnf(c_1392,plain,
    ( g1_orders_2(X1,X0) != k7_lattice3(sK0)
    | k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1125,c_11,c_21,c_557,c_1126])).

cnf(c_1393,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = X0
    | g1_orders_2(X1,X0) != k7_lattice3(sK0) ),
    inference(renaming,[status(thm)],[c_1392])).

cnf(c_2262,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) ),
    inference(superposition,[status(thm)],[c_2255,c_1393])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,k3_relset_1(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_442,plain,
    ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_978,plain,
    ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = u1_orders_2(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_442])).

cnf(c_3336,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = u1_orders_2(sK0) ),
    inference(superposition,[status(thm)],[c_434,c_978])).

cnf(c_5532,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) = u1_orders_2(sK0) ),
    inference(demodulation,[status(thm)],[c_2262,c_3336])).

cnf(c_8091,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = k7_lattice3(k7_lattice3(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2597,c_2261,c_5367,c_5532])).

cnf(c_9,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_8093,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8091,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:51:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.34/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.98  
% 3.34/0.98  ------  iProver source info
% 3.34/0.98  
% 3.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.98  git: non_committed_changes: false
% 3.34/0.98  git: last_make_outside_of_git: false
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     num_symb
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       true
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  ------ Parsing...
% 3.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.98  ------ Proving...
% 3.34/0.98  ------ Problem Properties 
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  clauses                                 11
% 3.34/0.98  conjectures                             2
% 3.34/0.98  EPR                                     1
% 3.34/0.98  Horn                                    11
% 3.34/0.98  unary                                   2
% 3.34/0.98  binary                                  6
% 3.34/0.98  lits                                    23
% 3.34/0.98  lits eq                                 8
% 3.34/0.98  fd_pure                                 0
% 3.34/0.98  fd_pseudo                               0
% 3.34/0.98  fd_cond                                 0
% 3.34/0.98  fd_pseudo_cond                          2
% 3.34/0.98  AC symbols                              0
% 3.34/0.98  
% 3.34/0.98  ------ Schedule dynamic 5 is on 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  Current options:
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     none
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       false
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ Proving...
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS status Theorem for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98   Resolution empty clause
% 3.34/0.98  
% 3.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  fof(f5,axiom,(
% 3.34/0.98    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f15,plain,(
% 3.34/0.98    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f5])).
% 3.34/0.98  
% 3.34/0.98  fof(f26,plain,(
% 3.34/0.98    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f15])).
% 3.34/0.98  
% 3.34/0.98  fof(f8,conjecture,(
% 3.34/0.98    ! [X0] : (l1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f9,negated_conjecture,(
% 3.34/0.98    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)))),
% 3.34/0.98    inference(negated_conjecture,[],[f8])).
% 3.34/0.98  
% 3.34/0.98  fof(f18,plain,(
% 3.34/0.98    ? [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0)) & l1_orders_2(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f9])).
% 3.34/0.98  
% 3.34/0.98  fof(f19,plain,(
% 3.34/0.98    ? [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0)) & l1_orders_2(X0)) => (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) & l1_orders_2(sK0))),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f20,plain,(
% 3.34/0.98    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) & l1_orders_2(sK0)),
% 3.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.34/0.98  
% 3.34/0.98  fof(f30,plain,(
% 3.34/0.98    l1_orders_2(sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f20])).
% 3.34/0.98  
% 3.34/0.98  fof(f4,axiom,(
% 3.34/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f14,plain,(
% 3.34/0.98    ! [X0,X1] : ((l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.34/0.98    inference(ennf_transformation,[],[f4])).
% 3.34/0.98  
% 3.34/0.98  fof(f25,plain,(
% 3.34/0.98    ( ! [X0,X1] : (l1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f14])).
% 3.34/0.98  
% 3.34/0.98  fof(f7,axiom,(
% 3.34/0.98    ! [X0] : (l1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f17,plain,(
% 3.34/0.98    ! [X0] : (g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) | ~l1_orders_2(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f7])).
% 3.34/0.98  
% 3.34/0.98  fof(f29,plain,(
% 3.34/0.98    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f17])).
% 3.34/0.98  
% 3.34/0.98  fof(f1,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f10,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f1])).
% 3.34/0.98  
% 3.34/0.98  fof(f21,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f10])).
% 3.34/0.98  
% 3.34/0.98  fof(f3,axiom,(
% 3.34/0.98    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f12,plain,(
% 3.34/0.98    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f3])).
% 3.34/0.98  
% 3.34/0.98  fof(f13,plain,(
% 3.34/0.98    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 3.34/0.98    inference(flattening,[],[f12])).
% 3.34/0.98  
% 3.34/0.98  fof(f23,plain,(
% 3.34/0.98    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f13])).
% 3.34/0.98  
% 3.34/0.98  fof(f24,plain,(
% 3.34/0.98    ( ! [X0,X1] : (v1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f14])).
% 3.34/0.98  
% 3.34/0.98  fof(f6,axiom,(
% 3.34/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f16,plain,(
% 3.34/0.98    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.34/0.98    inference(ennf_transformation,[],[f6])).
% 3.34/0.98  
% 3.34/0.98  fof(f27,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f16])).
% 3.34/0.98  
% 3.34/0.98  fof(f28,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f16])).
% 3.34/0.98  
% 3.34/0.98  fof(f2,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2)),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f11,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f2])).
% 3.34/0.98  
% 3.34/0.98  fof(f22,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f11])).
% 3.34/0.98  
% 3.34/0.98  fof(f31,plain,(
% 3.34/0.98    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))),
% 3.34/0.98    inference(cnf_transformation,[],[f20])).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.34/0.98      | ~ l1_orders_2(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_438,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 3.34/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10,negated_conjecture,
% 3.34/0.98      ( l1_orders_2(sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_434,plain,
% 3.34/0.98      ( l1_orders_2(sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | l1_orders_2(g1_orders_2(X1,X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_440,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.34/0.98      | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_613,plain,
% 3.34/0.98      ( l1_orders_2(X0) != iProver_top
% 3.34/0.98      | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_438,c_440]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8,plain,
% 3.34/0.98      ( ~ l1_orders_2(X0)
% 3.34/0.98      | g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_435,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
% 3.34/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_769,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),k3_relset_1(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))))) = k7_lattice3(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
% 3.34/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_613,c_435]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1401,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k3_relset_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) = k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_434,c_769]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_0,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f21]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_443,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_986,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.34/0.98      | l1_orders_2(g1_orders_2(X1,k3_relset_1(X1,X1,X0))) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_443,c_440]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1747,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) != iProver_top
% 3.34/0.98      | l1_orders_2(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1401,c_986]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2163,plain,
% 3.34/0.98      ( l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) != iProver_top
% 3.34/0.98      | l1_orders_2(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_438,c_1747]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_11,plain,
% 3.34/0.98      ( l1_orders_2(sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_19,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 3.34/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_21,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
% 3.34/0.98      | l1_orders_2(sK0) != iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_516,plain,
% 3.34/0.98      ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.34/0.98      | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_517,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) != iProver_top
% 3.34/0.98      | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_519,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
% 3.34/0.98      | l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_517]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2589,plain,
% 3.34/0.98      ( l1_orders_2(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2163,c_11,c_21,c_519]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2597,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),k3_relset_1(u1_struct_0(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),u1_struct_0(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),u1_orders_2(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) = k7_lattice3(k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2589,c_435]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_768,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(sK0) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_434,c_435]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1615,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
% 3.34/0.98      | l1_orders_2(k7_lattice3(sK0)) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_768,c_986]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1803,plain,
% 3.34/0.98      ( l1_orders_2(k7_lattice3(sK0)) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_1615,c_11,c_21]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2,plain,
% 3.34/0.98      ( ~ l1_orders_2(X0)
% 3.34/0.98      | ~ v1_orders_2(X0)
% 3.34/0.98      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f23]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_441,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
% 3.34/0.98      | l1_orders_2(X0) != iProver_top
% 3.34/0.98      | v1_orders_2(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1809,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = k7_lattice3(sK0)
% 3.34/0.98      | v1_orders_2(k7_lattice3(sK0)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1803,c_441]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | v1_orders_2(g1_orders_2(X1,X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f24]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_439,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.34/0.98      | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_987,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.34/0.98      | v1_orders_2(g1_orders_2(X1,k3_relset_1(X1,X1,X0))) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_443,c_439]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1650,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
% 3.34/0.98      | v1_orders_2(k7_lattice3(sK0)) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_768,c_987]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2255,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = k7_lattice3(sK0) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_1809,c_11,c_21,c_1650]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | X2 = X1
% 3.34/0.98      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_436,plain,
% 3.34/0.98      ( X0 = X1
% 3.34/0.98      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 3.34/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1123,plain,
% 3.34/0.98      ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
% 3.34/0.98      | u1_struct_0(sK0) = X0
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_768,c_436]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_554,plain,
% 3.34/0.98      ( m1_subset_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.34/0.98      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_555,plain,
% 3.34/0.98      ( m1_subset_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 3.34/0.98      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_557,plain,
% 3.34/0.98      ( m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
% 3.34/0.98      | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_555]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1124,plain,
% 3.34/0.98      ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
% 3.34/0.98      | u1_struct_0(sK0) = X0
% 3.34/0.98      | m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_768,c_436]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1254,plain,
% 3.34/0.98      ( u1_struct_0(sK0) = X0 | g1_orders_2(X0,X1) != k7_lattice3(sK0) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_1123,c_11,c_21,c_557,c_1124]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1255,plain,
% 3.34/0.98      ( g1_orders_2(X0,X1) != k7_lattice3(sK0) | u1_struct_0(sK0) = X0 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_1254]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2261,plain,
% 3.34/0.98      ( u1_struct_0(k7_lattice3(sK0)) = u1_struct_0(sK0) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2255,c_1255]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_878,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
% 3.34/0.98      | l1_orders_2(X0) != iProver_top
% 3.34/0.98      | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_613,c_441]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_575,plain,
% 3.34/0.98      ( ~ l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
% 3.34/0.98      | ~ v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
% 3.34/0.98      | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_581,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
% 3.34/0.98      | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top
% 3.34/0.98      | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_614,plain,
% 3.34/0.98      ( l1_orders_2(X0) != iProver_top
% 3.34/0.98      | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_438,c_439]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2224,plain,
% 3.34/0.98      ( l1_orders_2(X0) != iProver_top
% 3.34/0.98      | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_878,c_581,c_613,c_614]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2225,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
% 3.34/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_2224]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2232,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_434,c_2225]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | X2 = X0
% 3.34/0.98      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_437,plain,
% 3.34/0.98      ( X0 = X1
% 3.34/0.98      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2617,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 3.34/0.98      | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2232,c_437]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_20,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
% 3.34/0.98      | ~ l1_orders_2(sK0) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_518,plain,
% 3.34/0.98      ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
% 3.34/0.98      | l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_516]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2199,plain,
% 3.34/0.98      ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
% 3.34/0.98      | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2618,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 3.34/0.98      | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1
% 3.34/0.98      | m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2232,c_437]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2665,plain,
% 3.34/0.98      ( ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
% 3.34/0.98      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 3.34/0.98      | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1 ),
% 3.34/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2618]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3212,plain,
% 3.34/0.98      ( u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1
% 3.34/0.98      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2617,c_10,c_20,c_518,c_2199,c_2665]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3213,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 3.34/0.98      | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_3212]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3221,plain,
% 3.34/0.98      ( u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_orders_2(sK0) ),
% 3.34/0.98      inference(equality_resolution,[status(thm)],[c_3213]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2615,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 3.34/0.98      | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2232,c_436]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2616,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 3.34/0.98      | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0
% 3.34/0.98      | m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2232,c_436]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2659,plain,
% 3.34/0.98      ( ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
% 3.34/0.98      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 3.34/0.98      | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0 ),
% 3.34/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2616]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2901,plain,
% 3.34/0.98      ( u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0
% 3.34/0.98      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2615,c_10,c_20,c_518,c_2199,c_2659]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2902,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 3.34/0.98      | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_2901]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2910,plain,
% 3.34/0.98      ( u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_struct_0(sK0) ),
% 3.34/0.98      inference(equality_resolution,[status(thm)],[c_2902]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4656,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) = k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_2910,c_1401]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5356,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_3221,c_4656]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5367,plain,
% 3.34/0.98      ( k7_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(sK0) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_5356,c_768]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1125,plain,
% 3.34/0.98      ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = X0
% 3.34/0.98      | g1_orders_2(X1,X0) != k7_lattice3(sK0)
% 3.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_768,c_437]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1126,plain,
% 3.34/0.98      ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = X0
% 3.34/0.98      | g1_orders_2(X1,X0) != k7_lattice3(sK0)
% 3.34/0.98      | m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_768,c_437]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1392,plain,
% 3.34/0.98      ( g1_orders_2(X1,X0) != k7_lattice3(sK0)
% 3.34/0.98      | k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = X0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_1125,c_11,c_21,c_557,c_1126]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1393,plain,
% 3.34/0.98      ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = X0
% 3.34/0.98      | g1_orders_2(X1,X0) != k7_lattice3(sK0) ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_1392]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2262,plain,
% 3.34/0.98      ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2255,c_1393]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k3_relset_1(X1,X2,k3_relset_1(X1,X2,X0)) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_442,plain,
% 3.34/0.98      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_978,plain,
% 3.34/0.98      ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = u1_orders_2(X0)
% 3.34/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_438,c_442]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3336,plain,
% 3.34/0.98      ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = u1_orders_2(sK0) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_434,c_978]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5532,plain,
% 3.34/0.98      ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) = u1_orders_2(sK0) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_2262,c_3336]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8091,plain,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = k7_lattice3(k7_lattice3(sK0)) ),
% 3.34/0.98      inference(light_normalisation,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2597,c_2261,c_5367,c_5532]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9,negated_conjecture,
% 3.34/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8093,plain,
% 3.34/0.98      ( $false ),
% 3.34/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_8091,c_9]) ).
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  ------                               Statistics
% 3.34/0.98  
% 3.34/0.98  ------ General
% 3.34/0.98  
% 3.34/0.98  abstr_ref_over_cycles:                  0
% 3.34/0.98  abstr_ref_under_cycles:                 0
% 3.34/0.98  gc_basic_clause_elim:                   0
% 3.34/0.98  forced_gc_time:                         0
% 3.34/0.98  parsing_time:                           0.009
% 3.34/0.98  unif_index_cands_time:                  0.
% 3.34/0.98  unif_index_add_time:                    0.
% 3.34/0.98  orderings_time:                         0.
% 3.34/0.98  out_proof_time:                         0.008
% 3.34/0.98  total_time:                             0.295
% 3.34/0.98  num_of_symbols:                         42
% 3.34/0.98  num_of_terms:                           11640
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing
% 3.34/0.98  
% 3.34/0.98  num_of_splits:                          0
% 3.34/0.98  num_of_split_atoms:                     0
% 3.34/0.98  num_of_reused_defs:                     0
% 3.34/0.98  num_eq_ax_congr_red:                    0
% 3.34/0.98  num_of_sem_filtered_clauses:            1
% 3.34/0.98  num_of_subtypes:                        0
% 3.34/0.98  monotx_restored_types:                  0
% 3.34/0.98  sat_num_of_epr_types:                   0
% 3.34/0.98  sat_num_of_non_cyclic_types:            0
% 3.34/0.98  sat_guarded_non_collapsed_types:        0
% 3.34/0.98  num_pure_diseq_elim:                    0
% 3.34/0.98  simp_replaced_by:                       0
% 3.34/0.98  res_preprocessed:                       58
% 3.34/0.98  prep_upred:                             0
% 3.34/0.98  prep_unflattend:                        7
% 3.34/0.98  smt_new_axioms:                         0
% 3.34/0.98  pred_elim_cands:                        3
% 3.34/0.98  pred_elim:                              0
% 3.34/0.98  pred_elim_cl:                           0
% 3.34/0.98  pred_elim_cycles:                       2
% 3.34/0.98  merged_defs:                            0
% 3.34/0.98  merged_defs_ncl:                        0
% 3.34/0.98  bin_hyper_res:                          0
% 3.34/0.98  prep_cycles:                            3
% 3.34/0.98  pred_elim_time:                         0.002
% 3.34/0.98  splitting_time:                         0.
% 3.34/0.98  sem_filter_time:                        0.
% 3.34/0.98  monotx_time:                            0.001
% 3.34/0.98  subtype_inf_time:                       0.
% 3.34/0.98  
% 3.34/0.98  ------ Problem properties
% 3.34/0.98  
% 3.34/0.98  clauses:                                11
% 3.34/0.98  conjectures:                            2
% 3.34/0.98  epr:                                    1
% 3.34/0.98  horn:                                   11
% 3.34/0.98  ground:                                 2
% 3.34/0.98  unary:                                  2
% 3.34/0.98  binary:                                 6
% 3.34/0.98  lits:                                   23
% 3.34/0.98  lits_eq:                                8
% 3.34/0.98  fd_pure:                                0
% 3.34/0.98  fd_pseudo:                              0
% 3.34/0.98  fd_cond:                                0
% 3.34/0.98  fd_pseudo_cond:                         2
% 3.34/0.98  ac_symbols:                             0
% 3.34/0.98  
% 3.34/0.98  ------ Propositional Solver
% 3.34/0.98  
% 3.34/0.98  prop_solver_calls:                      25
% 3.34/0.98  prop_fast_solver_calls:                 580
% 3.34/0.98  smt_solver_calls:                       0
% 3.34/0.98  smt_fast_solver_calls:                  0
% 3.34/0.98  prop_num_of_clauses:                    3039
% 3.34/0.98  prop_preprocess_simplified:             6985
% 3.34/0.98  prop_fo_subsumed:                       27
% 3.34/0.98  prop_solver_time:                       0.
% 3.34/0.98  smt_solver_time:                        0.
% 3.34/0.98  smt_fast_solver_time:                   0.
% 3.34/0.98  prop_fast_solver_time:                  0.
% 3.34/0.98  prop_unsat_core_time:                   0.
% 3.34/0.98  
% 3.34/0.98  ------ QBF
% 3.34/0.98  
% 3.34/0.98  qbf_q_res:                              0
% 3.34/0.98  qbf_num_tautologies:                    0
% 3.34/0.98  qbf_prep_cycles:                        0
% 3.34/0.98  
% 3.34/0.98  ------ BMC1
% 3.34/0.98  
% 3.34/0.98  bmc1_current_bound:                     -1
% 3.34/0.98  bmc1_last_solved_bound:                 -1
% 3.34/0.98  bmc1_unsat_core_size:                   -1
% 3.34/0.98  bmc1_unsat_core_parents_size:           -1
% 3.34/0.98  bmc1_merge_next_fun:                    0
% 3.34/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation
% 3.34/0.98  
% 3.34/0.98  inst_num_of_clauses:                    1148
% 3.34/0.98  inst_num_in_passive:                    400
% 3.34/0.98  inst_num_in_active:                     503
% 3.34/0.98  inst_num_in_unprocessed:                245
% 3.34/0.98  inst_num_of_loops:                      510
% 3.34/0.98  inst_num_of_learning_restarts:          0
% 3.34/0.98  inst_num_moves_active_passive:          4
% 3.34/0.98  inst_lit_activity:                      0
% 3.34/0.98  inst_lit_activity_moves:                0
% 3.34/0.98  inst_num_tautologies:                   0
% 3.34/0.98  inst_num_prop_implied:                  0
% 3.34/0.98  inst_num_existing_simplified:           0
% 3.34/0.98  inst_num_eq_res_simplified:             0
% 3.34/0.98  inst_num_child_elim:                    0
% 3.34/0.98  inst_num_of_dismatching_blockings:      1244
% 3.34/0.98  inst_num_of_non_proper_insts:           1860
% 3.34/0.98  inst_num_of_duplicates:                 0
% 3.34/0.98  inst_inst_num_from_inst_to_res:         0
% 3.34/0.98  inst_dismatching_checking_time:         0.
% 3.34/0.98  
% 3.34/0.98  ------ Resolution
% 3.34/0.98  
% 3.34/0.98  res_num_of_clauses:                     0
% 3.34/0.98  res_num_in_passive:                     0
% 3.34/0.98  res_num_in_active:                      0
% 3.34/0.98  res_num_of_loops:                       61
% 3.34/0.98  res_forward_subset_subsumed:            172
% 3.34/0.99  res_backward_subset_subsumed:           0
% 3.34/0.99  res_forward_subsumed:                   0
% 3.34/0.99  res_backward_subsumed:                  0
% 3.34/0.99  res_forward_subsumption_resolution:     0
% 3.34/0.99  res_backward_subsumption_resolution:    0
% 3.34/0.99  res_clause_to_clause_subsumption:       322
% 3.34/0.99  res_orphan_elimination:                 0
% 3.34/0.99  res_tautology_del:                      118
% 3.34/0.99  res_num_eq_res_simplified:              0
% 3.34/0.99  res_num_sel_changes:                    0
% 3.34/0.99  res_moves_from_active_to_pass:          0
% 3.34/0.99  
% 3.34/0.99  ------ Superposition
% 3.34/0.99  
% 3.34/0.99  sup_time_total:                         0.
% 3.34/0.99  sup_time_generating:                    0.
% 3.34/0.99  sup_time_sim_full:                      0.
% 3.34/0.99  sup_time_sim_immed:                     0.
% 3.34/0.99  
% 3.34/0.99  sup_num_of_clauses:                     141
% 3.34/0.99  sup_num_in_active:                      63
% 3.34/0.99  sup_num_in_passive:                     78
% 3.34/0.99  sup_num_of_loops:                       101
% 3.34/0.99  sup_fw_superposition:                   122
% 3.34/0.99  sup_bw_superposition:                   140
% 3.34/0.99  sup_immediate_simplified:               68
% 3.34/0.99  sup_given_eliminated:                   3
% 3.34/0.99  comparisons_done:                       0
% 3.34/0.99  comparisons_avoided:                    0
% 3.34/0.99  
% 3.34/0.99  ------ Simplifications
% 3.34/0.99  
% 3.34/0.99  
% 3.34/0.99  sim_fw_subset_subsumed:                 39
% 3.34/0.99  sim_bw_subset_subsumed:                 11
% 3.34/0.99  sim_fw_subsumed:                        3
% 3.34/0.99  sim_bw_subsumed:                        0
% 3.34/0.99  sim_fw_subsumption_res:                 3
% 3.34/0.99  sim_bw_subsumption_res:                 0
% 3.34/0.99  sim_tautology_del:                      4
% 3.34/0.99  sim_eq_tautology_del:                   50
% 3.34/0.99  sim_eq_res_simp:                        0
% 3.34/0.99  sim_fw_demodulated:                     1
% 3.34/0.99  sim_bw_demodulated:                     42
% 3.34/0.99  sim_light_normalised:                   42
% 3.34/0.99  sim_joinable_taut:                      0
% 3.34/0.99  sim_joinable_simp:                      0
% 3.34/0.99  sim_ac_normalised:                      0
% 3.34/0.99  sim_smt_subsumption:                    0
% 3.34/0.99  
%------------------------------------------------------------------------------
