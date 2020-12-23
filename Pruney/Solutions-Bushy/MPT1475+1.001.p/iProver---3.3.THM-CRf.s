%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1475+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:42 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 497 expanded)
%              Number of clauses        :   46 ( 204 expanded)
%              Number of leaves         :    8 (  95 expanded)
%              Depth                    :   20
%              Number of atoms          :  158 (1118 expanded)
%              Number of equality atoms :   98 ( 505 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,
    ( ? [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_9,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_490,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_495,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(k7_lattice3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_496,plain,
    ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_756,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),k3_relset_1(u1_struct_0(k7_lattice3(X0)),u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))) = k7_lattice3(k7_lattice3(X0))
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_495,c_496])).

cnf(c_2092,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),k3_relset_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) = k7_lattice3(k7_lattice3(sK0)) ),
    inference(superposition,[status(thm)],[c_490,c_756])).

cnf(c_757,plain,
    ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(sK0) ),
    inference(superposition,[status(thm)],[c_490,c_496])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( ~ l1_orders_2(X0)
    | v1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_114,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | k7_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_115,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(k7_lattice3(X0))
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_119,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_115,c_2])).

cnf(c_489,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_119])).

cnf(c_583,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = k7_lattice3(sK0) ),
    inference(superposition,[status(thm)],[c_490,c_489])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_492,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_846,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_struct_0(k7_lattice3(sK0)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_492])).

cnf(c_1245,plain,
    ( u1_struct_0(k7_lattice3(sK0)) = u1_struct_0(sK0)
    | m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_757,c_846])).

cnf(c_10,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_24,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(k7_lattice3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_26,plain,
    ( l1_orders_2(k7_lattice3(sK0)) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_494,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_986,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_757,c_492])).

cnf(c_1166,plain,
    ( u1_struct_0(k7_lattice3(sK0)) = u1_struct_0(sK0)
    | m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_986])).

cnf(c_1239,plain,
    ( u1_struct_0(k7_lattice3(sK0)) = u1_struct_0(sK0)
    | l1_orders_2(k7_lattice3(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_1166])).

cnf(c_1367,plain,
    ( u1_struct_0(k7_lattice3(sK0)) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_10,c_26,c_1239])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_493,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_872,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_orders_2(k7_lattice3(sK0)) = X1
    | m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_493])).

cnf(c_1374,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
    | l1_orders_2(k7_lattice3(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_494])).

cnf(c_1371,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) = k7_lattice3(sK0) ),
    inference(demodulation,[status(thm)],[c_1367,c_583])).

cnf(c_1491,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_orders_2(k7_lattice3(sK0)) = X1
    | m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_493])).

cnf(c_1937,plain,
    ( u1_orders_2(k7_lattice3(sK0)) = X1
    | g1_orders_2(X0,X1) != k7_lattice3(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_872,c_10,c_26,c_1374,c_1491])).

cnf(c_1938,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
    | u1_orders_2(k7_lattice3(sK0)) = X1 ),
    inference(renaming,[status(thm)],[c_1937])).

cnf(c_1942,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) ),
    inference(superposition,[status(thm)],[c_757,c_1938])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,k3_relset_1(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_491,plain,
    ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_749,plain,
    ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = u1_orders_2(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_491])).

cnf(c_1640,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = u1_orders_2(sK0) ),
    inference(superposition,[status(thm)],[c_490,c_749])).

cnf(c_1953,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) = u1_orders_2(sK0) ),
    inference(demodulation,[status(thm)],[c_1942,c_1640])).

cnf(c_2094,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = k7_lattice3(k7_lattice3(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2092,c_1367,c_1953])).

cnf(c_8,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2094,c_8])).


%------------------------------------------------------------------------------
