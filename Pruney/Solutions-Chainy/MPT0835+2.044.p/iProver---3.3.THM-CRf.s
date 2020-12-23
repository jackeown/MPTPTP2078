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
% DateTime   : Thu Dec  3 11:56:15 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 269 expanded)
%              Number of clauses        :   67 ( 115 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  269 ( 651 expanded)
%              Number of equality atoms :  151 ( 356 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_227,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_228,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_588,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_871,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_588])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1085,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1086,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_1993,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_871,c_1086])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_594,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_312,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_4,c_10])).

cnf(c_587,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_3669,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_587])).

cnf(c_3963,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1993,c_3669])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_591,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1999,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1993,c_591])).

cnf(c_4052,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3963,c_1999])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_589,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1691,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_589])).

cnf(c_2594,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_1993,c_1691])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_593,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_590,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1998,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1993,c_590])).

cnf(c_2106,plain,
    ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_593,c_1998])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2114,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2106,c_12])).

cnf(c_2639,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2594,c_2114])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_287,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_288,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_739,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_288])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_278,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_279,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_697,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_279])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_817,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_697,c_20])).

cnf(c_1131,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_739,c_817])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_242,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_243,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_779,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_243])).

cnf(c_1211,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_779,c_697])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_251,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_252,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_815,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_252])).

cnf(c_1285,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_815,c_739])).

cnf(c_1289,plain,
    ( k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1131,c_1211,c_1285])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_260,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_261,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_742,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_261])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_269,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_270,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_775,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_270])).

cnf(c_1290,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1289,c_742,c_775])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4052,c_2639,c_1290])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:07:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.61/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/0.97  
% 2.61/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.61/0.97  
% 2.61/0.97  ------  iProver source info
% 2.61/0.97  
% 2.61/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.61/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.61/0.97  git: non_committed_changes: false
% 2.61/0.97  git: last_make_outside_of_git: false
% 2.61/0.97  
% 2.61/0.97  ------ 
% 2.61/0.97  
% 2.61/0.97  ------ Input Options
% 2.61/0.97  
% 2.61/0.97  --out_options                           all
% 2.61/0.97  --tptp_safe_out                         true
% 2.61/0.97  --problem_path                          ""
% 2.61/0.97  --include_path                          ""
% 2.61/0.97  --clausifier                            res/vclausify_rel
% 2.61/0.97  --clausifier_options                    --mode clausify
% 2.61/0.97  --stdin                                 false
% 2.61/0.97  --stats_out                             all
% 2.61/0.97  
% 2.61/0.97  ------ General Options
% 2.61/0.97  
% 2.61/0.97  --fof                                   false
% 2.61/0.97  --time_out_real                         305.
% 2.61/0.97  --time_out_virtual                      -1.
% 2.61/0.97  --symbol_type_check                     false
% 2.61/0.97  --clausify_out                          false
% 2.61/0.97  --sig_cnt_out                           false
% 2.61/0.97  --trig_cnt_out                          false
% 2.61/0.97  --trig_cnt_out_tolerance                1.
% 2.61/0.97  --trig_cnt_out_sk_spl                   false
% 2.61/0.97  --abstr_cl_out                          false
% 2.61/0.97  
% 2.61/0.97  ------ Global Options
% 2.61/0.97  
% 2.61/0.97  --schedule                              default
% 2.61/0.97  --add_important_lit                     false
% 2.61/0.97  --prop_solver_per_cl                    1000
% 2.61/0.97  --min_unsat_core                        false
% 2.61/0.97  --soft_assumptions                      false
% 2.61/0.97  --soft_lemma_size                       3
% 2.61/0.97  --prop_impl_unit_size                   0
% 2.61/0.97  --prop_impl_unit                        []
% 2.61/0.97  --share_sel_clauses                     true
% 2.61/0.97  --reset_solvers                         false
% 2.61/0.97  --bc_imp_inh                            [conj_cone]
% 2.61/0.97  --conj_cone_tolerance                   3.
% 2.61/0.97  --extra_neg_conj                        none
% 2.61/0.97  --large_theory_mode                     true
% 2.61/0.97  --prolific_symb_bound                   200
% 2.61/0.97  --lt_threshold                          2000
% 2.61/0.97  --clause_weak_htbl                      true
% 2.61/0.97  --gc_record_bc_elim                     false
% 2.61/0.97  
% 2.61/0.97  ------ Preprocessing Options
% 2.61/0.97  
% 2.61/0.97  --preprocessing_flag                    true
% 2.61/0.97  --time_out_prep_mult                    0.1
% 2.61/0.97  --splitting_mode                        input
% 2.61/0.97  --splitting_grd                         true
% 2.61/0.97  --splitting_cvd                         false
% 2.61/0.97  --splitting_cvd_svl                     false
% 2.61/0.97  --splitting_nvd                         32
% 2.61/0.97  --sub_typing                            true
% 2.61/0.97  --prep_gs_sim                           true
% 2.61/0.97  --prep_unflatten                        true
% 2.61/0.97  --prep_res_sim                          true
% 2.61/0.97  --prep_upred                            true
% 2.61/0.97  --prep_sem_filter                       exhaustive
% 2.61/0.97  --prep_sem_filter_out                   false
% 2.61/0.97  --pred_elim                             true
% 2.61/0.97  --res_sim_input                         true
% 2.61/0.97  --eq_ax_congr_red                       true
% 2.61/0.97  --pure_diseq_elim                       true
% 2.61/0.97  --brand_transform                       false
% 2.61/0.97  --non_eq_to_eq                          false
% 2.61/0.97  --prep_def_merge                        true
% 2.61/0.97  --prep_def_merge_prop_impl              false
% 2.61/0.97  --prep_def_merge_mbd                    true
% 2.61/0.97  --prep_def_merge_tr_red                 false
% 2.61/0.97  --prep_def_merge_tr_cl                  false
% 2.61/0.97  --smt_preprocessing                     true
% 2.61/0.97  --smt_ac_axioms                         fast
% 2.61/0.97  --preprocessed_out                      false
% 2.61/0.97  --preprocessed_stats                    false
% 2.61/0.97  
% 2.61/0.97  ------ Abstraction refinement Options
% 2.61/0.97  
% 2.61/0.97  --abstr_ref                             []
% 2.61/0.97  --abstr_ref_prep                        false
% 2.61/0.97  --abstr_ref_until_sat                   false
% 2.61/0.97  --abstr_ref_sig_restrict                funpre
% 2.61/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/0.97  --abstr_ref_under                       []
% 2.61/0.97  
% 2.61/0.97  ------ SAT Options
% 2.61/0.97  
% 2.61/0.97  --sat_mode                              false
% 2.61/0.97  --sat_fm_restart_options                ""
% 2.61/0.97  --sat_gr_def                            false
% 2.61/0.97  --sat_epr_types                         true
% 2.61/0.97  --sat_non_cyclic_types                  false
% 2.61/0.97  --sat_finite_models                     false
% 2.61/0.97  --sat_fm_lemmas                         false
% 2.61/0.97  --sat_fm_prep                           false
% 2.61/0.97  --sat_fm_uc_incr                        true
% 2.61/0.97  --sat_out_model                         small
% 2.61/0.97  --sat_out_clauses                       false
% 2.61/0.97  
% 2.61/0.97  ------ QBF Options
% 2.61/0.97  
% 2.61/0.97  --qbf_mode                              false
% 2.61/0.97  --qbf_elim_univ                         false
% 2.61/0.97  --qbf_dom_inst                          none
% 2.61/0.97  --qbf_dom_pre_inst                      false
% 2.61/0.97  --qbf_sk_in                             false
% 2.61/0.97  --qbf_pred_elim                         true
% 2.61/0.97  --qbf_split                             512
% 2.61/0.97  
% 2.61/0.97  ------ BMC1 Options
% 2.61/0.97  
% 2.61/0.97  --bmc1_incremental                      false
% 2.61/0.97  --bmc1_axioms                           reachable_all
% 2.61/0.97  --bmc1_min_bound                        0
% 2.61/0.97  --bmc1_max_bound                        -1
% 2.61/0.97  --bmc1_max_bound_default                -1
% 2.61/0.97  --bmc1_symbol_reachability              true
% 2.61/0.97  --bmc1_property_lemmas                  false
% 2.61/0.97  --bmc1_k_induction                      false
% 2.61/0.97  --bmc1_non_equiv_states                 false
% 2.61/0.97  --bmc1_deadlock                         false
% 2.61/0.97  --bmc1_ucm                              false
% 2.61/0.97  --bmc1_add_unsat_core                   none
% 2.61/0.97  --bmc1_unsat_core_children              false
% 2.61/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/0.97  --bmc1_out_stat                         full
% 2.61/0.97  --bmc1_ground_init                      false
% 2.61/0.97  --bmc1_pre_inst_next_state              false
% 2.61/0.97  --bmc1_pre_inst_state                   false
% 2.61/0.97  --bmc1_pre_inst_reach_state             false
% 2.61/0.97  --bmc1_out_unsat_core                   false
% 2.61/0.97  --bmc1_aig_witness_out                  false
% 2.61/0.97  --bmc1_verbose                          false
% 2.61/0.97  --bmc1_dump_clauses_tptp                false
% 2.61/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.61/0.97  --bmc1_dump_file                        -
% 2.61/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.61/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.61/0.97  --bmc1_ucm_extend_mode                  1
% 2.61/0.97  --bmc1_ucm_init_mode                    2
% 2.61/0.97  --bmc1_ucm_cone_mode                    none
% 2.61/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.61/0.97  --bmc1_ucm_relax_model                  4
% 2.61/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.61/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/0.97  --bmc1_ucm_layered_model                none
% 2.61/0.97  --bmc1_ucm_max_lemma_size               10
% 2.61/0.97  
% 2.61/0.97  ------ AIG Options
% 2.61/0.97  
% 2.61/0.97  --aig_mode                              false
% 2.61/0.97  
% 2.61/0.97  ------ Instantiation Options
% 2.61/0.97  
% 2.61/0.97  --instantiation_flag                    true
% 2.61/0.97  --inst_sos_flag                         false
% 2.61/0.97  --inst_sos_phase                        true
% 2.61/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/0.97  --inst_lit_sel_side                     num_symb
% 2.61/0.97  --inst_solver_per_active                1400
% 2.61/0.97  --inst_solver_calls_frac                1.
% 2.61/0.97  --inst_passive_queue_type               priority_queues
% 2.61/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/0.97  --inst_passive_queues_freq              [25;2]
% 2.61/0.97  --inst_dismatching                      true
% 2.61/0.97  --inst_eager_unprocessed_to_passive     true
% 2.61/0.97  --inst_prop_sim_given                   true
% 2.61/0.97  --inst_prop_sim_new                     false
% 2.61/0.97  --inst_subs_new                         false
% 2.61/0.97  --inst_eq_res_simp                      false
% 2.61/0.97  --inst_subs_given                       false
% 2.61/0.97  --inst_orphan_elimination               true
% 2.61/0.97  --inst_learning_loop_flag               true
% 2.61/0.97  --inst_learning_start                   3000
% 2.61/0.97  --inst_learning_factor                  2
% 2.61/0.97  --inst_start_prop_sim_after_learn       3
% 2.61/0.97  --inst_sel_renew                        solver
% 2.61/0.97  --inst_lit_activity_flag                true
% 2.61/0.97  --inst_restr_to_given                   false
% 2.61/0.97  --inst_activity_threshold               500
% 2.61/0.97  --inst_out_proof                        true
% 2.61/0.97  
% 2.61/0.97  ------ Resolution Options
% 2.61/0.97  
% 2.61/0.97  --resolution_flag                       true
% 2.61/0.97  --res_lit_sel                           adaptive
% 2.61/0.97  --res_lit_sel_side                      none
% 2.61/0.97  --res_ordering                          kbo
% 2.61/0.97  --res_to_prop_solver                    active
% 2.61/0.97  --res_prop_simpl_new                    false
% 2.61/0.97  --res_prop_simpl_given                  true
% 2.61/0.97  --res_passive_queue_type                priority_queues
% 2.61/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/0.97  --res_passive_queues_freq               [15;5]
% 2.61/0.97  --res_forward_subs                      full
% 2.61/0.97  --res_backward_subs                     full
% 2.61/0.97  --res_forward_subs_resolution           true
% 2.61/0.97  --res_backward_subs_resolution          true
% 2.61/0.97  --res_orphan_elimination                true
% 2.61/0.97  --res_time_limit                        2.
% 2.61/0.97  --res_out_proof                         true
% 2.61/0.97  
% 2.61/0.97  ------ Superposition Options
% 2.61/0.97  
% 2.61/0.97  --superposition_flag                    true
% 2.61/0.97  --sup_passive_queue_type                priority_queues
% 2.61/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.61/0.97  --demod_completeness_check              fast
% 2.61/0.97  --demod_use_ground                      true
% 2.61/0.97  --sup_to_prop_solver                    passive
% 2.61/0.97  --sup_prop_simpl_new                    true
% 2.61/0.97  --sup_prop_simpl_given                  true
% 2.61/0.97  --sup_fun_splitting                     false
% 2.61/0.97  --sup_smt_interval                      50000
% 2.61/0.97  
% 2.61/0.97  ------ Superposition Simplification Setup
% 2.61/0.97  
% 2.61/0.97  --sup_indices_passive                   []
% 2.61/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.97  --sup_full_bw                           [BwDemod]
% 2.61/0.97  --sup_immed_triv                        [TrivRules]
% 2.61/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.97  --sup_immed_bw_main                     []
% 2.61/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/0.97  
% 2.61/0.97  ------ Combination Options
% 2.61/0.97  
% 2.61/0.97  --comb_res_mult                         3
% 2.61/0.97  --comb_sup_mult                         2
% 2.61/0.97  --comb_inst_mult                        10
% 2.61/0.97  
% 2.61/0.97  ------ Debug Options
% 2.61/0.97  
% 2.61/0.97  --dbg_backtrace                         false
% 2.61/0.97  --dbg_dump_prop_clauses                 false
% 2.61/0.97  --dbg_dump_prop_clauses_file            -
% 2.61/0.97  --dbg_out_stat                          false
% 2.61/0.97  ------ Parsing...
% 2.61/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.61/0.97  
% 2.61/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.61/0.97  
% 2.61/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.61/0.97  
% 2.61/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.61/0.97  ------ Proving...
% 2.61/0.97  ------ Problem Properties 
% 2.61/0.97  
% 2.61/0.97  
% 2.61/0.97  clauses                                 18
% 2.61/0.97  conjectures                             1
% 2.61/0.97  EPR                                     2
% 2.61/0.97  Horn                                    18
% 2.61/0.97  unary                                   5
% 2.61/0.97  binary                                  8
% 2.61/0.97  lits                                    36
% 2.61/0.97  lits eq                                 22
% 2.61/0.97  fd_pure                                 0
% 2.61/0.97  fd_pseudo                               0
% 2.61/0.97  fd_cond                                 0
% 2.61/0.97  fd_pseudo_cond                          1
% 2.61/0.97  AC symbols                              0
% 2.61/0.97  
% 2.61/0.97  ------ Schedule dynamic 5 is on 
% 2.61/0.97  
% 2.61/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.61/0.97  
% 2.61/0.97  
% 2.61/0.97  ------ 
% 2.61/0.97  Current options:
% 2.61/0.97  ------ 
% 2.61/0.97  
% 2.61/0.97  ------ Input Options
% 2.61/0.97  
% 2.61/0.97  --out_options                           all
% 2.61/0.97  --tptp_safe_out                         true
% 2.61/0.97  --problem_path                          ""
% 2.61/0.97  --include_path                          ""
% 2.61/0.97  --clausifier                            res/vclausify_rel
% 2.61/0.97  --clausifier_options                    --mode clausify
% 2.61/0.97  --stdin                                 false
% 2.61/0.97  --stats_out                             all
% 2.61/0.97  
% 2.61/0.97  ------ General Options
% 2.61/0.97  
% 2.61/0.97  --fof                                   false
% 2.61/0.97  --time_out_real                         305.
% 2.61/0.97  --time_out_virtual                      -1.
% 2.61/0.97  --symbol_type_check                     false
% 2.61/0.97  --clausify_out                          false
% 2.61/0.97  --sig_cnt_out                           false
% 2.61/0.97  --trig_cnt_out                          false
% 2.61/0.97  --trig_cnt_out_tolerance                1.
% 2.61/0.97  --trig_cnt_out_sk_spl                   false
% 2.61/0.97  --abstr_cl_out                          false
% 2.61/0.97  
% 2.61/0.97  ------ Global Options
% 2.61/0.97  
% 2.61/0.97  --schedule                              default
% 2.61/0.97  --add_important_lit                     false
% 2.61/0.97  --prop_solver_per_cl                    1000
% 2.61/0.97  --min_unsat_core                        false
% 2.61/0.97  --soft_assumptions                      false
% 2.61/0.97  --soft_lemma_size                       3
% 2.61/0.97  --prop_impl_unit_size                   0
% 2.61/0.97  --prop_impl_unit                        []
% 2.61/0.97  --share_sel_clauses                     true
% 2.61/0.97  --reset_solvers                         false
% 2.61/0.97  --bc_imp_inh                            [conj_cone]
% 2.61/0.97  --conj_cone_tolerance                   3.
% 2.61/0.97  --extra_neg_conj                        none
% 2.61/0.97  --large_theory_mode                     true
% 2.61/0.97  --prolific_symb_bound                   200
% 2.61/0.97  --lt_threshold                          2000
% 2.61/0.97  --clause_weak_htbl                      true
% 2.61/0.97  --gc_record_bc_elim                     false
% 2.61/0.97  
% 2.61/0.97  ------ Preprocessing Options
% 2.61/0.97  
% 2.61/0.97  --preprocessing_flag                    true
% 2.61/0.97  --time_out_prep_mult                    0.1
% 2.61/0.97  --splitting_mode                        input
% 2.61/0.97  --splitting_grd                         true
% 2.61/0.97  --splitting_cvd                         false
% 2.61/0.97  --splitting_cvd_svl                     false
% 2.61/0.97  --splitting_nvd                         32
% 2.61/0.97  --sub_typing                            true
% 2.61/0.97  --prep_gs_sim                           true
% 2.61/0.97  --prep_unflatten                        true
% 2.61/0.97  --prep_res_sim                          true
% 2.61/0.97  --prep_upred                            true
% 2.61/0.97  --prep_sem_filter                       exhaustive
% 2.61/0.97  --prep_sem_filter_out                   false
% 2.61/0.97  --pred_elim                             true
% 2.61/0.97  --res_sim_input                         true
% 2.61/0.97  --eq_ax_congr_red                       true
% 2.61/0.97  --pure_diseq_elim                       true
% 2.61/0.97  --brand_transform                       false
% 2.61/0.97  --non_eq_to_eq                          false
% 2.61/0.97  --prep_def_merge                        true
% 2.61/0.97  --prep_def_merge_prop_impl              false
% 2.61/0.97  --prep_def_merge_mbd                    true
% 2.61/0.97  --prep_def_merge_tr_red                 false
% 2.61/0.97  --prep_def_merge_tr_cl                  false
% 2.61/0.97  --smt_preprocessing                     true
% 2.61/0.97  --smt_ac_axioms                         fast
% 2.61/0.97  --preprocessed_out                      false
% 2.61/0.97  --preprocessed_stats                    false
% 2.61/0.97  
% 2.61/0.97  ------ Abstraction refinement Options
% 2.61/0.97  
% 2.61/0.97  --abstr_ref                             []
% 2.61/0.97  --abstr_ref_prep                        false
% 2.61/0.97  --abstr_ref_until_sat                   false
% 2.61/0.97  --abstr_ref_sig_restrict                funpre
% 2.61/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/0.97  --abstr_ref_under                       []
% 2.61/0.97  
% 2.61/0.97  ------ SAT Options
% 2.61/0.97  
% 2.61/0.97  --sat_mode                              false
% 2.61/0.97  --sat_fm_restart_options                ""
% 2.61/0.97  --sat_gr_def                            false
% 2.61/0.97  --sat_epr_types                         true
% 2.61/0.97  --sat_non_cyclic_types                  false
% 2.61/0.97  --sat_finite_models                     false
% 2.61/0.97  --sat_fm_lemmas                         false
% 2.61/0.97  --sat_fm_prep                           false
% 2.61/0.97  --sat_fm_uc_incr                        true
% 2.61/0.97  --sat_out_model                         small
% 2.61/0.97  --sat_out_clauses                       false
% 2.61/0.97  
% 2.61/0.97  ------ QBF Options
% 2.61/0.97  
% 2.61/0.97  --qbf_mode                              false
% 2.61/0.97  --qbf_elim_univ                         false
% 2.61/0.97  --qbf_dom_inst                          none
% 2.61/0.97  --qbf_dom_pre_inst                      false
% 2.61/0.97  --qbf_sk_in                             false
% 2.61/0.97  --qbf_pred_elim                         true
% 2.61/0.97  --qbf_split                             512
% 2.61/0.97  
% 2.61/0.97  ------ BMC1 Options
% 2.61/0.97  
% 2.61/0.97  --bmc1_incremental                      false
% 2.61/0.97  --bmc1_axioms                           reachable_all
% 2.61/0.97  --bmc1_min_bound                        0
% 2.61/0.97  --bmc1_max_bound                        -1
% 2.61/0.97  --bmc1_max_bound_default                -1
% 2.61/0.97  --bmc1_symbol_reachability              true
% 2.61/0.97  --bmc1_property_lemmas                  false
% 2.61/0.97  --bmc1_k_induction                      false
% 2.61/0.97  --bmc1_non_equiv_states                 false
% 2.61/0.97  --bmc1_deadlock                         false
% 2.61/0.97  --bmc1_ucm                              false
% 2.61/0.97  --bmc1_add_unsat_core                   none
% 2.61/0.97  --bmc1_unsat_core_children              false
% 2.61/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/0.97  --bmc1_out_stat                         full
% 2.61/0.97  --bmc1_ground_init                      false
% 2.61/0.97  --bmc1_pre_inst_next_state              false
% 2.61/0.97  --bmc1_pre_inst_state                   false
% 2.61/0.97  --bmc1_pre_inst_reach_state             false
% 2.61/0.97  --bmc1_out_unsat_core                   false
% 2.61/0.97  --bmc1_aig_witness_out                  false
% 2.61/0.97  --bmc1_verbose                          false
% 2.61/0.97  --bmc1_dump_clauses_tptp                false
% 2.61/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.61/0.97  --bmc1_dump_file                        -
% 2.61/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.61/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.61/0.97  --bmc1_ucm_extend_mode                  1
% 2.61/0.97  --bmc1_ucm_init_mode                    2
% 2.61/0.97  --bmc1_ucm_cone_mode                    none
% 2.61/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.61/0.97  --bmc1_ucm_relax_model                  4
% 2.61/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.61/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/0.97  --bmc1_ucm_layered_model                none
% 2.61/0.97  --bmc1_ucm_max_lemma_size               10
% 2.61/0.97  
% 2.61/0.97  ------ AIG Options
% 2.61/0.97  
% 2.61/0.97  --aig_mode                              false
% 2.61/0.97  
% 2.61/0.97  ------ Instantiation Options
% 2.61/0.97  
% 2.61/0.97  --instantiation_flag                    true
% 2.61/0.97  --inst_sos_flag                         false
% 2.61/0.97  --inst_sos_phase                        true
% 2.61/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/0.97  --inst_lit_sel_side                     none
% 2.61/0.97  --inst_solver_per_active                1400
% 2.61/0.97  --inst_solver_calls_frac                1.
% 2.61/0.97  --inst_passive_queue_type               priority_queues
% 2.61/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/0.97  --inst_passive_queues_freq              [25;2]
% 2.61/0.97  --inst_dismatching                      true
% 2.61/0.97  --inst_eager_unprocessed_to_passive     true
% 2.61/0.97  --inst_prop_sim_given                   true
% 2.61/0.97  --inst_prop_sim_new                     false
% 2.61/0.97  --inst_subs_new                         false
% 2.61/0.97  --inst_eq_res_simp                      false
% 2.61/0.97  --inst_subs_given                       false
% 2.61/0.97  --inst_orphan_elimination               true
% 2.61/0.97  --inst_learning_loop_flag               true
% 2.61/0.97  --inst_learning_start                   3000
% 2.61/0.97  --inst_learning_factor                  2
% 2.61/0.97  --inst_start_prop_sim_after_learn       3
% 2.61/0.97  --inst_sel_renew                        solver
% 2.61/0.97  --inst_lit_activity_flag                true
% 2.61/0.97  --inst_restr_to_given                   false
% 2.61/0.97  --inst_activity_threshold               500
% 2.61/0.97  --inst_out_proof                        true
% 2.61/0.97  
% 2.61/0.97  ------ Resolution Options
% 2.61/0.97  
% 2.61/0.97  --resolution_flag                       false
% 2.61/0.97  --res_lit_sel                           adaptive
% 2.61/0.97  --res_lit_sel_side                      none
% 2.61/0.97  --res_ordering                          kbo
% 2.61/0.97  --res_to_prop_solver                    active
% 2.61/0.97  --res_prop_simpl_new                    false
% 2.61/0.97  --res_prop_simpl_given                  true
% 2.61/0.97  --res_passive_queue_type                priority_queues
% 2.61/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/0.97  --res_passive_queues_freq               [15;5]
% 2.61/0.97  --res_forward_subs                      full
% 2.61/0.97  --res_backward_subs                     full
% 2.61/0.97  --res_forward_subs_resolution           true
% 2.61/0.97  --res_backward_subs_resolution          true
% 2.61/0.97  --res_orphan_elimination                true
% 2.61/0.97  --res_time_limit                        2.
% 2.61/0.97  --res_out_proof                         true
% 2.61/0.97  
% 2.61/0.97  ------ Superposition Options
% 2.61/0.97  
% 2.61/0.97  --superposition_flag                    true
% 2.61/0.97  --sup_passive_queue_type                priority_queues
% 2.61/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.61/0.97  --demod_completeness_check              fast
% 2.61/0.97  --demod_use_ground                      true
% 2.61/0.97  --sup_to_prop_solver                    passive
% 2.61/0.97  --sup_prop_simpl_new                    true
% 2.61/0.97  --sup_prop_simpl_given                  true
% 2.61/0.97  --sup_fun_splitting                     false
% 2.61/0.97  --sup_smt_interval                      50000
% 2.61/0.97  
% 2.61/0.97  ------ Superposition Simplification Setup
% 2.61/0.97  
% 2.61/0.97  --sup_indices_passive                   []
% 2.61/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.97  --sup_full_bw                           [BwDemod]
% 2.61/0.97  --sup_immed_triv                        [TrivRules]
% 2.61/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.97  --sup_immed_bw_main                     []
% 2.61/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/0.97  
% 2.61/0.97  ------ Combination Options
% 2.61/0.97  
% 2.61/0.97  --comb_res_mult                         3
% 2.61/0.97  --comb_sup_mult                         2
% 2.61/0.97  --comb_inst_mult                        10
% 2.61/0.97  
% 2.61/0.97  ------ Debug Options
% 2.61/0.97  
% 2.61/0.97  --dbg_backtrace                         false
% 2.61/0.97  --dbg_dump_prop_clauses                 false
% 2.61/0.97  --dbg_dump_prop_clauses_file            -
% 2.61/0.97  --dbg_out_stat                          false
% 2.61/0.97  
% 2.61/0.97  
% 2.61/0.97  
% 2.61/0.97  
% 2.61/0.97  ------ Proving...
% 2.61/0.97  
% 2.61/0.97  
% 2.61/0.97  % SZS status Theorem for theBenchmark.p
% 2.61/0.97  
% 2.61/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.61/0.97  
% 2.61/0.97  fof(f2,axiom,(
% 2.61/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f18,plain,(
% 2.61/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.61/0.97    inference(ennf_transformation,[],[f2])).
% 2.61/0.97  
% 2.61/0.97  fof(f40,plain,(
% 2.61/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.61/0.97    inference(cnf_transformation,[],[f18])).
% 2.61/0.97  
% 2.61/0.97  fof(f16,conjecture,(
% 2.61/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f17,negated_conjecture,(
% 2.61/0.97    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.61/0.97    inference(negated_conjecture,[],[f16])).
% 2.61/0.97  
% 2.61/0.97  fof(f31,plain,(
% 2.61/0.97    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.61/0.97    inference(ennf_transformation,[],[f17])).
% 2.61/0.97  
% 2.61/0.97  fof(f35,plain,(
% 2.61/0.97    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 2.61/0.97    introduced(choice_axiom,[])).
% 2.61/0.97  
% 2.61/0.97  fof(f36,plain,(
% 2.61/0.97    (k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.61/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).
% 2.61/0.97  
% 2.61/0.97  fof(f57,plain,(
% 2.61/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.61/0.97    inference(cnf_transformation,[],[f36])).
% 2.61/0.97  
% 2.61/0.97  fof(f5,axiom,(
% 2.61/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f44,plain,(
% 2.61/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.61/0.97    inference(cnf_transformation,[],[f5])).
% 2.61/0.97  
% 2.61/0.97  fof(f1,axiom,(
% 2.61/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f32,plain,(
% 2.61/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.61/0.97    inference(nnf_transformation,[],[f1])).
% 2.61/0.97  
% 2.61/0.97  fof(f33,plain,(
% 2.61/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.61/0.97    inference(flattening,[],[f32])).
% 2.61/0.97  
% 2.61/0.97  fof(f38,plain,(
% 2.61/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.61/0.97    inference(cnf_transformation,[],[f33])).
% 2.61/0.97  
% 2.61/0.97  fof(f59,plain,(
% 2.61/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.61/0.97    inference(equality_resolution,[],[f38])).
% 2.61/0.97  
% 2.61/0.97  fof(f3,axiom,(
% 2.61/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f19,plain,(
% 2.61/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.61/0.97    inference(ennf_transformation,[],[f3])).
% 2.61/0.97  
% 2.61/0.97  fof(f34,plain,(
% 2.61/0.97    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.61/0.97    inference(nnf_transformation,[],[f19])).
% 2.61/0.97  
% 2.61/0.97  fof(f42,plain,(
% 2.61/0.97    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.61/0.97    inference(cnf_transformation,[],[f34])).
% 2.61/0.97  
% 2.61/0.97  fof(f8,axiom,(
% 2.61/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f22,plain,(
% 2.61/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.61/0.97    inference(ennf_transformation,[],[f8])).
% 2.61/0.97  
% 2.61/0.97  fof(f23,plain,(
% 2.61/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/0.97    inference(flattening,[],[f22])).
% 2.61/0.97  
% 2.61/0.97  fof(f47,plain,(
% 2.61/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.61/0.97    inference(cnf_transformation,[],[f23])).
% 2.61/0.97  
% 2.61/0.97  fof(f6,axiom,(
% 2.61/0.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f20,plain,(
% 2.61/0.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/0.97    inference(ennf_transformation,[],[f6])).
% 2.61/0.97  
% 2.61/0.97  fof(f45,plain,(
% 2.61/0.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.61/0.97    inference(cnf_transformation,[],[f20])).
% 2.61/0.97  
% 2.61/0.97  fof(f10,axiom,(
% 2.61/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f24,plain,(
% 2.61/0.97    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.61/0.97    inference(ennf_transformation,[],[f10])).
% 2.61/0.97  
% 2.61/0.97  fof(f25,plain,(
% 2.61/0.97    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.61/0.97    inference(flattening,[],[f24])).
% 2.61/0.97  
% 2.61/0.97  fof(f50,plain,(
% 2.61/0.97    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.61/0.97    inference(cnf_transformation,[],[f25])).
% 2.61/0.97  
% 2.61/0.97  fof(f4,axiom,(
% 2.61/0.97    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f43,plain,(
% 2.61/0.97    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.61/0.97    inference(cnf_transformation,[],[f4])).
% 2.61/0.97  
% 2.61/0.97  fof(f7,axiom,(
% 2.61/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f21,plain,(
% 2.61/0.97    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.61/0.97    inference(ennf_transformation,[],[f7])).
% 2.61/0.97  
% 2.61/0.97  fof(f46,plain,(
% 2.61/0.97    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.61/0.97    inference(cnf_transformation,[],[f21])).
% 2.61/0.97  
% 2.61/0.97  fof(f9,axiom,(
% 2.61/0.97    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f48,plain,(
% 2.61/0.97    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.61/0.97    inference(cnf_transformation,[],[f9])).
% 2.61/0.97  
% 2.61/0.97  fof(f11,axiom,(
% 2.61/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f26,plain,(
% 2.61/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/0.97    inference(ennf_transformation,[],[f11])).
% 2.61/0.97  
% 2.61/0.97  fof(f51,plain,(
% 2.61/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/0.97    inference(cnf_transformation,[],[f26])).
% 2.61/0.97  
% 2.61/0.97  fof(f12,axiom,(
% 2.61/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f27,plain,(
% 2.61/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/0.97    inference(ennf_transformation,[],[f12])).
% 2.61/0.97  
% 2.61/0.97  fof(f52,plain,(
% 2.61/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/0.97    inference(cnf_transformation,[],[f27])).
% 2.61/0.97  
% 2.61/0.97  fof(f58,plain,(
% 2.61/0.97    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 2.61/0.97    inference(cnf_transformation,[],[f36])).
% 2.61/0.97  
% 2.61/0.97  fof(f15,axiom,(
% 2.61/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f30,plain,(
% 2.61/0.97    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/0.97    inference(ennf_transformation,[],[f15])).
% 2.61/0.97  
% 2.61/0.97  fof(f55,plain,(
% 2.61/0.97    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/0.97    inference(cnf_transformation,[],[f30])).
% 2.61/0.97  
% 2.61/0.97  fof(f56,plain,(
% 2.61/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/0.97    inference(cnf_transformation,[],[f30])).
% 2.61/0.97  
% 2.61/0.97  fof(f14,axiom,(
% 2.61/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f29,plain,(
% 2.61/0.97    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/0.97    inference(ennf_transformation,[],[f14])).
% 2.61/0.97  
% 2.61/0.97  fof(f54,plain,(
% 2.61/0.97    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/0.97    inference(cnf_transformation,[],[f29])).
% 2.61/0.97  
% 2.61/0.97  fof(f13,axiom,(
% 2.61/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.61/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/0.97  
% 2.61/0.97  fof(f28,plain,(
% 2.61/0.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/0.97    inference(ennf_transformation,[],[f13])).
% 2.61/0.97  
% 2.61/0.97  fof(f53,plain,(
% 2.61/0.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/0.97    inference(cnf_transformation,[],[f28])).
% 2.61/0.97  
% 2.61/0.97  cnf(c_3,plain,
% 2.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.61/0.97      | ~ v1_relat_1(X1)
% 2.61/0.97      | v1_relat_1(X0) ),
% 2.61/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_21,negated_conjecture,
% 2.61/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.61/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_227,plain,
% 2.61/0.97      ( ~ v1_relat_1(X0)
% 2.61/0.97      | v1_relat_1(X1)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 2.61/0.97      | sK2 != X1 ),
% 2.61/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_228,plain,
% 2.61/0.97      ( ~ v1_relat_1(X0)
% 2.61/0.97      | v1_relat_1(sK2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
% 2.61/0.97      inference(unflattening,[status(thm)],[c_227]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_588,plain,
% 2.61/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 2.61/0.97      | v1_relat_1(X0) != iProver_top
% 2.61/0.97      | v1_relat_1(sK2) = iProver_top ),
% 2.61/0.97      inference(predicate_to_equality,[status(thm)],[c_228]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_871,plain,
% 2.61/0.97      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.61/0.97      | v1_relat_1(sK2) = iProver_top ),
% 2.61/0.97      inference(equality_resolution,[status(thm)],[c_588]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_7,plain,
% 2.61/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.61/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1085,plain,
% 2.61/0.97      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.61/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1086,plain,
% 2.61/0.97      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.61/0.97      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1993,plain,
% 2.61/0.97      ( v1_relat_1(sK2) = iProver_top ),
% 2.61/0.97      inference(global_propositional_subsumption,
% 2.61/0.97                [status(thm)],
% 2.61/0.97                [c_871,c_1086]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1,plain,
% 2.61/0.97      ( r1_tarski(X0,X0) ),
% 2.61/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_594,plain,
% 2.61/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 2.61/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_4,plain,
% 2.61/0.97      ( v4_relat_1(X0,X1)
% 2.61/0.97      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.61/0.97      | ~ v1_relat_1(X0) ),
% 2.61/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_10,plain,
% 2.61/0.97      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.61/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_312,plain,
% 2.61/0.97      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.61/0.97      | ~ v1_relat_1(X0)
% 2.61/0.97      | k7_relat_1(X0,X1) = X0 ),
% 2.61/0.97      inference(resolution,[status(thm)],[c_4,c_10]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_587,plain,
% 2.61/0.97      ( k7_relat_1(X0,X1) = X0
% 2.61/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.61/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.61/0.97      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_3669,plain,
% 2.61/0.97      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.61/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_594,c_587]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_3963,plain,
% 2.61/0.97      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_1993,c_3669]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_8,plain,
% 2.61/0.97      ( ~ v1_relat_1(X0)
% 2.61/0.97      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.61/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_591,plain,
% 2.61/0.97      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.61/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.61/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1999,plain,
% 2.61/0.97      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_1993,c_591]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_4052,plain,
% 2.61/0.97      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_3963,c_1999]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_13,plain,
% 2.61/0.97      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.61/0.97      | ~ v1_relat_1(X0)
% 2.61/0.97      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.61/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_589,plain,
% 2.61/0.97      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.61/0.97      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.61/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.61/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1691,plain,
% 2.61/0.97      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 2.61/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_594,c_589]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_2594,plain,
% 2.61/0.97      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_1993,c_1691]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_6,plain,
% 2.61/0.97      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.61/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_593,plain,
% 2.61/0.97      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.61/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_9,plain,
% 2.61/0.97      ( ~ v1_relat_1(X0)
% 2.61/0.97      | ~ v1_relat_1(X1)
% 2.61/0.97      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 2.61/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_590,plain,
% 2.61/0.97      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.61/0.97      | v1_relat_1(X0) != iProver_top
% 2.61/0.97      | v1_relat_1(X1) != iProver_top ),
% 2.61/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1998,plain,
% 2.61/0.97      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 2.61/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_1993,c_590]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_2106,plain,
% 2.61/0.97      ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_593,c_1998]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_12,plain,
% 2.61/0.97      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.61/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_2114,plain,
% 2.61/0.97      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 2.61/0.97      inference(light_normalisation,[status(thm)],[c_2106,c_12]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_2639,plain,
% 2.61/0.97      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/0.97      inference(superposition,[status(thm)],[c_2594,c_2114]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_14,plain,
% 2.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.61/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_287,plain,
% 2.61/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.61/0.97      | sK2 != X2 ),
% 2.61/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_288,plain,
% 2.61/0.97      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.61/0.97      inference(unflattening,[status(thm)],[c_287]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_739,plain,
% 2.61/0.97      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 2.61/0.97      inference(equality_resolution,[status(thm)],[c_288]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_15,plain,
% 2.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.61/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_278,plain,
% 2.61/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.61/0.97      | sK2 != X2 ),
% 2.61/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_279,plain,
% 2.61/0.97      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.61/0.97      inference(unflattening,[status(thm)],[c_278]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_697,plain,
% 2.61/0.97      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 2.61/0.97      inference(equality_resolution,[status(thm)],[c_279]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_20,negated_conjecture,
% 2.61/0.97      ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
% 2.61/0.97      | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
% 2.61/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_817,plain,
% 2.61/0.97      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.61/0.97      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.61/0.97      inference(demodulation,[status(thm)],[c_697,c_20]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1131,plain,
% 2.61/0.97      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
% 2.61/0.97      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.61/0.97      inference(demodulation,[status(thm)],[c_739,c_817]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_19,plain,
% 2.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/0.97      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 2.61/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_242,plain,
% 2.61/0.97      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.61/0.97      | sK2 != X2 ),
% 2.61/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_243,plain,
% 2.61/0.97      ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.61/0.97      inference(unflattening,[status(thm)],[c_242]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_779,plain,
% 2.61/0.97      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
% 2.61/0.97      inference(equality_resolution,[status(thm)],[c_243]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1211,plain,
% 2.61/0.97      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
% 2.61/0.97      inference(light_normalisation,[status(thm)],[c_779,c_697]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_18,plain,
% 2.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/0.97      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.61/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_251,plain,
% 2.61/0.97      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.61/0.97      | sK2 != X2 ),
% 2.61/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_252,plain,
% 2.61/0.97      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.61/0.97      inference(unflattening,[status(thm)],[c_251]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_815,plain,
% 2.61/0.97      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
% 2.61/0.97      inference(equality_resolution,[status(thm)],[c_252]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1285,plain,
% 2.61/0.97      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
% 2.61/0.97      inference(light_normalisation,[status(thm)],[c_815,c_739]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1289,plain,
% 2.61/0.97      ( k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.61/0.97      | k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.61/0.97      inference(light_normalisation,[status(thm)],[c_1131,c_1211,c_1285]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_17,plain,
% 2.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/0.97      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.61/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_260,plain,
% 2.61/0.97      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.61/0.97      | sK2 != X2 ),
% 2.61/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_261,plain,
% 2.61/0.97      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.61/0.97      inference(unflattening,[status(thm)],[c_260]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_742,plain,
% 2.61/0.97      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.61/0.97      inference(equality_resolution,[status(thm)],[c_261]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_16,plain,
% 2.61/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/0.97      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.61/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_269,plain,
% 2.61/0.97      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.61/0.97      | sK2 != X2 ),
% 2.61/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_270,plain,
% 2.61/0.97      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.61/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.61/0.97      inference(unflattening,[status(thm)],[c_269]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_775,plain,
% 2.61/0.97      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.61/0.97      inference(equality_resolution,[status(thm)],[c_270]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(c_1290,plain,
% 2.61/0.97      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.61/0.97      | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.61/0.97      inference(demodulation,[status(thm)],[c_1289,c_742,c_775]) ).
% 2.61/0.97  
% 2.61/0.97  cnf(contradiction,plain,
% 2.61/0.97      ( $false ),
% 2.61/0.97      inference(minisat,[status(thm)],[c_4052,c_2639,c_1290]) ).
% 2.61/0.97  
% 2.61/0.97  
% 2.61/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.61/0.97  
% 2.61/0.97  ------                               Statistics
% 2.61/0.97  
% 2.61/0.97  ------ General
% 2.61/0.97  
% 2.61/0.97  abstr_ref_over_cycles:                  0
% 2.61/0.97  abstr_ref_under_cycles:                 0
% 2.61/0.97  gc_basic_clause_elim:                   0
% 2.61/0.97  forced_gc_time:                         0
% 2.61/0.97  parsing_time:                           0.007
% 2.61/0.97  unif_index_cands_time:                  0.
% 2.61/0.97  unif_index_add_time:                    0.
% 2.61/0.97  orderings_time:                         0.
% 2.61/0.97  out_proof_time:                         0.007
% 2.61/0.97  total_time:                             0.152
% 2.61/0.97  num_of_symbols:                         51
% 2.61/0.97  num_of_terms:                           5392
% 2.61/0.97  
% 2.61/0.97  ------ Preprocessing
% 2.61/0.97  
% 2.61/0.97  num_of_splits:                          0
% 2.61/0.97  num_of_split_atoms:                     0
% 2.61/0.97  num_of_reused_defs:                     0
% 2.61/0.97  num_eq_ax_congr_red:                    22
% 2.61/0.97  num_of_sem_filtered_clauses:            1
% 2.61/0.97  num_of_subtypes:                        0
% 2.61/0.97  monotx_restored_types:                  0
% 2.61/0.97  sat_num_of_epr_types:                   0
% 2.61/0.97  sat_num_of_non_cyclic_types:            0
% 2.61/0.97  sat_guarded_non_collapsed_types:        0
% 2.61/0.97  num_pure_diseq_elim:                    0
% 2.61/0.97  simp_replaced_by:                       0
% 2.61/0.97  res_preprocessed:                       106
% 2.61/0.97  prep_upred:                             0
% 2.61/0.97  prep_unflattend:                        7
% 2.61/0.97  smt_new_axioms:                         0
% 2.61/0.97  pred_elim_cands:                        2
% 2.61/0.97  pred_elim:                              2
% 2.61/0.97  pred_elim_cl:                           3
% 2.61/0.97  pred_elim_cycles:                       4
% 2.61/0.97  merged_defs:                            0
% 2.61/0.97  merged_defs_ncl:                        0
% 2.61/0.97  bin_hyper_res:                          0
% 2.61/0.97  prep_cycles:                            4
% 2.61/0.97  pred_elim_time:                         0.002
% 2.61/0.97  splitting_time:                         0.
% 2.61/0.97  sem_filter_time:                        0.
% 2.61/0.97  monotx_time:                            0.
% 2.61/0.97  subtype_inf_time:                       0.
% 2.61/0.97  
% 2.61/0.97  ------ Problem properties
% 2.61/0.97  
% 2.61/0.97  clauses:                                18
% 2.61/0.97  conjectures:                            1
% 2.61/0.97  epr:                                    2
% 2.61/0.97  horn:                                   18
% 2.61/0.97  ground:                                 1
% 2.61/0.97  unary:                                  5
% 2.61/0.97  binary:                                 8
% 2.61/0.97  lits:                                   36
% 2.61/0.97  lits_eq:                                22
% 2.61/0.97  fd_pure:                                0
% 2.61/0.97  fd_pseudo:                              0
% 2.61/0.97  fd_cond:                                0
% 2.61/0.97  fd_pseudo_cond:                         1
% 2.61/0.97  ac_symbols:                             0
% 2.61/0.97  
% 2.61/0.97  ------ Propositional Solver
% 2.61/0.97  
% 2.61/0.97  prop_solver_calls:                      29
% 2.61/0.97  prop_fast_solver_calls:                 611
% 2.61/0.97  smt_solver_calls:                       0
% 2.61/0.97  smt_fast_solver_calls:                  0
% 2.61/0.97  prop_num_of_clauses:                    2033
% 2.61/0.97  prop_preprocess_simplified:             5014
% 2.61/0.97  prop_fo_subsumed:                       3
% 2.61/0.97  prop_solver_time:                       0.
% 2.61/0.97  smt_solver_time:                        0.
% 2.61/0.97  smt_fast_solver_time:                   0.
% 2.61/0.97  prop_fast_solver_time:                  0.
% 2.61/0.97  prop_unsat_core_time:                   0.
% 2.61/0.97  
% 2.61/0.97  ------ QBF
% 2.61/0.97  
% 2.61/0.97  qbf_q_res:                              0
% 2.61/0.97  qbf_num_tautologies:                    0
% 2.61/0.97  qbf_prep_cycles:                        0
% 2.61/0.98  
% 2.61/0.98  ------ BMC1
% 2.61/0.98  
% 2.61/0.98  bmc1_current_bound:                     -1
% 2.61/0.98  bmc1_last_solved_bound:                 -1
% 2.61/0.98  bmc1_unsat_core_size:                   -1
% 2.61/0.98  bmc1_unsat_core_parents_size:           -1
% 2.61/0.98  bmc1_merge_next_fun:                    0
% 2.61/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.61/0.98  
% 2.61/0.98  ------ Instantiation
% 2.61/0.98  
% 2.61/0.98  inst_num_of_clauses:                    668
% 2.61/0.98  inst_num_in_passive:                    241
% 2.61/0.98  inst_num_in_active:                     324
% 2.61/0.98  inst_num_in_unprocessed:                103
% 2.61/0.98  inst_num_of_loops:                      330
% 2.61/0.98  inst_num_of_learning_restarts:          0
% 2.61/0.98  inst_num_moves_active_passive:          3
% 2.61/0.98  inst_lit_activity:                      0
% 2.61/0.98  inst_lit_activity_moves:                0
% 2.61/0.98  inst_num_tautologies:                   0
% 2.61/0.98  inst_num_prop_implied:                  0
% 2.61/0.98  inst_num_existing_simplified:           0
% 2.61/0.98  inst_num_eq_res_simplified:             0
% 2.61/0.98  inst_num_child_elim:                    0
% 2.61/0.98  inst_num_of_dismatching_blockings:      64
% 2.61/0.98  inst_num_of_non_proper_insts:           536
% 2.61/0.98  inst_num_of_duplicates:                 0
% 2.61/0.98  inst_inst_num_from_inst_to_res:         0
% 2.61/0.98  inst_dismatching_checking_time:         0.
% 2.61/0.98  
% 2.61/0.98  ------ Resolution
% 2.61/0.98  
% 2.61/0.98  res_num_of_clauses:                     0
% 2.61/0.98  res_num_in_passive:                     0
% 2.61/0.98  res_num_in_active:                      0
% 2.61/0.98  res_num_of_loops:                       110
% 2.61/0.98  res_forward_subset_subsumed:            57
% 2.61/0.98  res_backward_subset_subsumed:           2
% 2.61/0.98  res_forward_subsumed:                   0
% 2.61/0.98  res_backward_subsumed:                  0
% 2.61/0.98  res_forward_subsumption_resolution:     0
% 2.61/0.98  res_backward_subsumption_resolution:    0
% 2.61/0.98  res_clause_to_clause_subsumption:       99
% 2.61/0.98  res_orphan_elimination:                 0
% 2.61/0.98  res_tautology_del:                      62
% 2.61/0.98  res_num_eq_res_simplified:              0
% 2.61/0.98  res_num_sel_changes:                    0
% 2.61/0.98  res_moves_from_active_to_pass:          0
% 2.61/0.98  
% 2.61/0.98  ------ Superposition
% 2.61/0.98  
% 2.61/0.98  sup_time_total:                         0.
% 2.61/0.98  sup_time_generating:                    0.
% 2.61/0.98  sup_time_sim_full:                      0.
% 2.61/0.98  sup_time_sim_immed:                     0.
% 2.61/0.98  
% 2.61/0.98  sup_num_of_clauses:                     72
% 2.61/0.98  sup_num_in_active:                      62
% 2.61/0.98  sup_num_in_passive:                     10
% 2.61/0.98  sup_num_of_loops:                       64
% 2.61/0.98  sup_fw_superposition:                   41
% 2.61/0.98  sup_bw_superposition:                   13
% 2.61/0.98  sup_immediate_simplified:               8
% 2.61/0.98  sup_given_eliminated:                   0
% 2.61/0.98  comparisons_done:                       0
% 2.61/0.98  comparisons_avoided:                    0
% 2.61/0.98  
% 2.61/0.98  ------ Simplifications
% 2.61/0.98  
% 2.61/0.98  
% 2.61/0.98  sim_fw_subset_subsumed:                 0
% 2.61/0.98  sim_bw_subset_subsumed:                 0
% 2.61/0.98  sim_fw_subsumed:                        0
% 2.61/0.98  sim_bw_subsumed:                        0
% 2.61/0.98  sim_fw_subsumption_res:                 0
% 2.61/0.98  sim_bw_subsumption_res:                 0
% 2.61/0.98  sim_tautology_del:                      0
% 2.61/0.98  sim_eq_tautology_del:                   4
% 2.61/0.98  sim_eq_res_simp:                        1
% 2.61/0.98  sim_fw_demodulated:                     4
% 2.61/0.98  sim_bw_demodulated:                     3
% 2.61/0.98  sim_light_normalised:                   9
% 2.61/0.98  sim_joinable_taut:                      0
% 2.61/0.98  sim_joinable_simp:                      0
% 2.61/0.98  sim_ac_normalised:                      0
% 2.61/0.98  sim_smt_subsumption:                    0
% 2.61/0.98  
%------------------------------------------------------------------------------
