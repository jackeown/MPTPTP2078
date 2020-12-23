%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:13 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 914 expanded)
%              Number of clauses        :   87 ( 415 expanded)
%              Number of leaves         :   18 ( 178 expanded)
%              Depth                    :   21
%              Number of atoms          :  318 (2313 expanded)
%              Number of equality atoms :  173 (1016 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f36])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_246,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_247,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_616,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_417,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_731,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_721,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_867,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_868,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_942,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_943,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_1251,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_731,c_868,c_943])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_623,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_618,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1658,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_618])).

cnf(c_4280,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_1251,c_1658])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_622,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_619,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2574,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_619])).

cnf(c_2848,plain,
    ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_622,c_2574])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2856,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2848,c_11])).

cnf(c_4290,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4280,c_2856])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_5])).

cnf(c_261,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_21])).

cnf(c_262,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_615,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_926,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_615])).

cnf(c_1362,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_926,c_731,c_868,c_943])).

cnf(c_1659,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_618])).

cnf(c_927,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_926])).

cnf(c_1282,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1295,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_2186,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1659,c_731,c_867,c_927,c_942,c_1295])).

cnf(c_13,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_617,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3170,plain,
    ( k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k5_relat_1(sK2,k6_relat_1(X0))
    | r1_tarski(k10_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2856,c_617])).

cnf(c_3620,plain,
    ( k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),k10_relat_1(sK2,X0)) = k5_relat_1(sK2,k6_relat_1(X0))
    | v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_3170])).

cnf(c_4073,plain,
    ( k7_relat_1(k5_relat_1(sK2,k6_relat_1(sK0)),k10_relat_1(sK2,sK0)) = k5_relat_1(sK2,k6_relat_1(sK0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2186,c_3620])).

cnf(c_3169,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2186,c_2856])).

cnf(c_4074,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4073,c_2186,c_3169])).

cnf(c_1281,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2669,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_2670,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4077,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4074,c_731,c_867,c_942,c_2669,c_2670])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_620,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1504,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1251,c_620])).

cnf(c_4081,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4077,c_1504])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_294,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_295,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_771,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_295])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_312,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_313,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_730,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_313])).

cnf(c_20,negated_conjecture,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_844,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_730,c_20])).

cnf(c_1108,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_771,c_844])).

cnf(c_1109,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1108,c_771])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_276,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_277,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_808,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_277])).

cnf(c_1170,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_808,c_730])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_285,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_286,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_811,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_286])).

cnf(c_1248,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_811,c_771])).

cnf(c_1415,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k2_relat_1(sK2)) != k10_relat_1(sK2,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1109,c_1170,c_1248])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_303,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_304,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_775,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_304])).

cnf(c_1416,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k10_relat_1(sK2,sK0)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1415,c_775])).

cnf(c_3183,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3169,c_1416])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4290,c_4081,c_3183])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:09:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.79/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.98  
% 2.79/0.98  ------  iProver source info
% 2.79/0.98  
% 2.79/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.98  git: non_committed_changes: false
% 2.79/0.98  git: last_make_outside_of_git: false
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  
% 2.79/0.98  ------ Input Options
% 2.79/0.98  
% 2.79/0.98  --out_options                           all
% 2.79/0.98  --tptp_safe_out                         true
% 2.79/0.98  --problem_path                          ""
% 2.79/0.98  --include_path                          ""
% 2.79/0.98  --clausifier                            res/vclausify_rel
% 2.79/0.98  --clausifier_options                    --mode clausify
% 2.79/0.98  --stdin                                 false
% 2.79/0.98  --stats_out                             all
% 2.79/0.98  
% 2.79/0.98  ------ General Options
% 2.79/0.98  
% 2.79/0.98  --fof                                   false
% 2.79/0.98  --time_out_real                         305.
% 2.79/0.98  --time_out_virtual                      -1.
% 2.79/0.98  --symbol_type_check                     false
% 2.79/0.98  --clausify_out                          false
% 2.79/0.98  --sig_cnt_out                           false
% 2.79/0.98  --trig_cnt_out                          false
% 2.79/0.98  --trig_cnt_out_tolerance                1.
% 2.79/0.98  --trig_cnt_out_sk_spl                   false
% 2.79/0.98  --abstr_cl_out                          false
% 2.79/0.98  
% 2.79/0.98  ------ Global Options
% 2.79/0.98  
% 2.79/0.98  --schedule                              default
% 2.79/0.98  --add_important_lit                     false
% 2.79/0.98  --prop_solver_per_cl                    1000
% 2.79/0.98  --min_unsat_core                        false
% 2.79/0.98  --soft_assumptions                      false
% 2.79/0.98  --soft_lemma_size                       3
% 2.79/0.98  --prop_impl_unit_size                   0
% 2.79/0.98  --prop_impl_unit                        []
% 2.79/0.98  --share_sel_clauses                     true
% 2.79/0.98  --reset_solvers                         false
% 2.79/0.98  --bc_imp_inh                            [conj_cone]
% 2.79/0.98  --conj_cone_tolerance                   3.
% 2.79/0.98  --extra_neg_conj                        none
% 2.79/0.98  --large_theory_mode                     true
% 2.79/0.98  --prolific_symb_bound                   200
% 2.79/0.98  --lt_threshold                          2000
% 2.79/0.98  --clause_weak_htbl                      true
% 2.79/0.98  --gc_record_bc_elim                     false
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing Options
% 2.79/0.98  
% 2.79/0.98  --preprocessing_flag                    true
% 2.79/0.98  --time_out_prep_mult                    0.1
% 2.79/0.98  --splitting_mode                        input
% 2.79/0.98  --splitting_grd                         true
% 2.79/0.98  --splitting_cvd                         false
% 2.79/0.98  --splitting_cvd_svl                     false
% 2.79/0.98  --splitting_nvd                         32
% 2.79/0.98  --sub_typing                            true
% 2.79/0.98  --prep_gs_sim                           true
% 2.79/0.98  --prep_unflatten                        true
% 2.79/0.98  --prep_res_sim                          true
% 2.79/0.98  --prep_upred                            true
% 2.79/0.98  --prep_sem_filter                       exhaustive
% 2.79/0.98  --prep_sem_filter_out                   false
% 2.79/0.98  --pred_elim                             true
% 2.79/0.98  --res_sim_input                         true
% 2.79/0.98  --eq_ax_congr_red                       true
% 2.79/0.98  --pure_diseq_elim                       true
% 2.79/0.98  --brand_transform                       false
% 2.79/0.98  --non_eq_to_eq                          false
% 2.79/0.98  --prep_def_merge                        true
% 2.79/0.98  --prep_def_merge_prop_impl              false
% 2.79/0.98  --prep_def_merge_mbd                    true
% 2.79/0.98  --prep_def_merge_tr_red                 false
% 2.79/0.98  --prep_def_merge_tr_cl                  false
% 2.79/0.98  --smt_preprocessing                     true
% 2.79/0.98  --smt_ac_axioms                         fast
% 2.79/0.98  --preprocessed_out                      false
% 2.79/0.98  --preprocessed_stats                    false
% 2.79/0.98  
% 2.79/0.98  ------ Abstraction refinement Options
% 2.79/0.98  
% 2.79/0.98  --abstr_ref                             []
% 2.79/0.98  --abstr_ref_prep                        false
% 2.79/0.98  --abstr_ref_until_sat                   false
% 2.79/0.98  --abstr_ref_sig_restrict                funpre
% 2.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.98  --abstr_ref_under                       []
% 2.79/0.98  
% 2.79/0.98  ------ SAT Options
% 2.79/0.98  
% 2.79/0.98  --sat_mode                              false
% 2.79/0.98  --sat_fm_restart_options                ""
% 2.79/0.98  --sat_gr_def                            false
% 2.79/0.98  --sat_epr_types                         true
% 2.79/0.98  --sat_non_cyclic_types                  false
% 2.79/0.98  --sat_finite_models                     false
% 2.79/0.98  --sat_fm_lemmas                         false
% 2.79/0.98  --sat_fm_prep                           false
% 2.79/0.98  --sat_fm_uc_incr                        true
% 2.79/0.98  --sat_out_model                         small
% 2.79/0.98  --sat_out_clauses                       false
% 2.79/0.98  
% 2.79/0.98  ------ QBF Options
% 2.79/0.98  
% 2.79/0.98  --qbf_mode                              false
% 2.79/0.98  --qbf_elim_univ                         false
% 2.79/0.98  --qbf_dom_inst                          none
% 2.79/0.98  --qbf_dom_pre_inst                      false
% 2.79/0.98  --qbf_sk_in                             false
% 2.79/0.98  --qbf_pred_elim                         true
% 2.79/0.98  --qbf_split                             512
% 2.79/0.98  
% 2.79/0.98  ------ BMC1 Options
% 2.79/0.98  
% 2.79/0.98  --bmc1_incremental                      false
% 2.79/0.98  --bmc1_axioms                           reachable_all
% 2.79/0.98  --bmc1_min_bound                        0
% 2.79/0.98  --bmc1_max_bound                        -1
% 2.79/0.98  --bmc1_max_bound_default                -1
% 2.79/0.98  --bmc1_symbol_reachability              true
% 2.79/0.98  --bmc1_property_lemmas                  false
% 2.79/0.98  --bmc1_k_induction                      false
% 2.79/0.98  --bmc1_non_equiv_states                 false
% 2.79/0.98  --bmc1_deadlock                         false
% 2.79/0.98  --bmc1_ucm                              false
% 2.79/0.98  --bmc1_add_unsat_core                   none
% 2.79/0.98  --bmc1_unsat_core_children              false
% 2.79/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.98  --bmc1_out_stat                         full
% 2.79/0.98  --bmc1_ground_init                      false
% 2.79/0.98  --bmc1_pre_inst_next_state              false
% 2.79/0.98  --bmc1_pre_inst_state                   false
% 2.79/0.98  --bmc1_pre_inst_reach_state             false
% 2.79/0.98  --bmc1_out_unsat_core                   false
% 2.79/0.98  --bmc1_aig_witness_out                  false
% 2.79/0.98  --bmc1_verbose                          false
% 2.79/0.98  --bmc1_dump_clauses_tptp                false
% 2.79/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.98  --bmc1_dump_file                        -
% 2.79/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.98  --bmc1_ucm_extend_mode                  1
% 2.79/0.98  --bmc1_ucm_init_mode                    2
% 2.79/0.98  --bmc1_ucm_cone_mode                    none
% 2.79/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.98  --bmc1_ucm_relax_model                  4
% 2.79/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.98  --bmc1_ucm_layered_model                none
% 2.79/0.98  --bmc1_ucm_max_lemma_size               10
% 2.79/0.98  
% 2.79/0.98  ------ AIG Options
% 2.79/0.98  
% 2.79/0.98  --aig_mode                              false
% 2.79/0.98  
% 2.79/0.98  ------ Instantiation Options
% 2.79/0.98  
% 2.79/0.98  --instantiation_flag                    true
% 2.79/0.98  --inst_sos_flag                         false
% 2.79/0.98  --inst_sos_phase                        true
% 2.79/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.98  --inst_lit_sel_side                     num_symb
% 2.79/0.98  --inst_solver_per_active                1400
% 2.79/0.98  --inst_solver_calls_frac                1.
% 2.79/0.98  --inst_passive_queue_type               priority_queues
% 2.79/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.98  --inst_passive_queues_freq              [25;2]
% 2.79/0.98  --inst_dismatching                      true
% 2.79/0.98  --inst_eager_unprocessed_to_passive     true
% 2.79/0.98  --inst_prop_sim_given                   true
% 2.79/0.98  --inst_prop_sim_new                     false
% 2.79/0.98  --inst_subs_new                         false
% 2.79/0.98  --inst_eq_res_simp                      false
% 2.79/0.98  --inst_subs_given                       false
% 2.79/0.98  --inst_orphan_elimination               true
% 2.79/0.98  --inst_learning_loop_flag               true
% 2.79/0.98  --inst_learning_start                   3000
% 2.79/0.98  --inst_learning_factor                  2
% 2.79/0.98  --inst_start_prop_sim_after_learn       3
% 2.79/0.98  --inst_sel_renew                        solver
% 2.79/0.98  --inst_lit_activity_flag                true
% 2.79/0.98  --inst_restr_to_given                   false
% 2.79/0.98  --inst_activity_threshold               500
% 2.79/0.98  --inst_out_proof                        true
% 2.79/0.98  
% 2.79/0.98  ------ Resolution Options
% 2.79/0.98  
% 2.79/0.98  --resolution_flag                       true
% 2.79/0.98  --res_lit_sel                           adaptive
% 2.79/0.98  --res_lit_sel_side                      none
% 2.79/0.98  --res_ordering                          kbo
% 2.79/0.98  --res_to_prop_solver                    active
% 2.79/0.98  --res_prop_simpl_new                    false
% 2.79/0.98  --res_prop_simpl_given                  true
% 2.79/0.98  --res_passive_queue_type                priority_queues
% 2.79/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.98  --res_passive_queues_freq               [15;5]
% 2.79/0.98  --res_forward_subs                      full
% 2.79/0.98  --res_backward_subs                     full
% 2.79/0.98  --res_forward_subs_resolution           true
% 2.79/0.98  --res_backward_subs_resolution          true
% 2.79/0.98  --res_orphan_elimination                true
% 2.79/0.98  --res_time_limit                        2.
% 2.79/0.98  --res_out_proof                         true
% 2.79/0.98  
% 2.79/0.98  ------ Superposition Options
% 2.79/0.98  
% 2.79/0.98  --superposition_flag                    true
% 2.79/0.98  --sup_passive_queue_type                priority_queues
% 2.79/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.98  --demod_completeness_check              fast
% 2.79/0.98  --demod_use_ground                      true
% 2.79/0.98  --sup_to_prop_solver                    passive
% 2.79/0.98  --sup_prop_simpl_new                    true
% 2.79/0.98  --sup_prop_simpl_given                  true
% 2.79/0.98  --sup_fun_splitting                     false
% 2.79/0.98  --sup_smt_interval                      50000
% 2.79/0.98  
% 2.79/0.98  ------ Superposition Simplification Setup
% 2.79/0.98  
% 2.79/0.98  --sup_indices_passive                   []
% 2.79/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_full_bw                           [BwDemod]
% 2.79/0.98  --sup_immed_triv                        [TrivRules]
% 2.79/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_immed_bw_main                     []
% 2.79/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.98  
% 2.79/0.98  ------ Combination Options
% 2.79/0.98  
% 2.79/0.98  --comb_res_mult                         3
% 2.79/0.98  --comb_sup_mult                         2
% 2.79/0.98  --comb_inst_mult                        10
% 2.79/0.98  
% 2.79/0.98  ------ Debug Options
% 2.79/0.98  
% 2.79/0.98  --dbg_backtrace                         false
% 2.79/0.98  --dbg_dump_prop_clauses                 false
% 2.79/0.98  --dbg_dump_prop_clauses_file            -
% 2.79/0.98  --dbg_out_stat                          false
% 2.79/0.98  ------ Parsing...
% 2.79/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/0.98  ------ Proving...
% 2.79/0.98  ------ Problem Properties 
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  clauses                                 18
% 2.79/0.98  conjectures                             1
% 3.00/0.98  EPR                                     2
% 3.00/0.98  Horn                                    18
% 3.00/0.98  unary                                   5
% 3.00/0.98  binary                                  7
% 3.00/0.98  lits                                    37
% 3.00/0.98  lits eq                                 21
% 3.00/0.98  fd_pure                                 0
% 3.00/0.98  fd_pseudo                               0
% 3.00/0.98  fd_cond                                 0
% 3.00/0.98  fd_pseudo_cond                          1
% 3.00/0.98  AC symbols                              0
% 3.00/0.98  
% 3.00/0.98  ------ Schedule dynamic 5 is on 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  ------ 
% 3.00/0.98  Current options:
% 3.00/0.98  ------ 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options
% 3.00/0.98  
% 3.00/0.98  --out_options                           all
% 3.00/0.98  --tptp_safe_out                         true
% 3.00/0.98  --problem_path                          ""
% 3.00/0.98  --include_path                          ""
% 3.00/0.98  --clausifier                            res/vclausify_rel
% 3.00/0.98  --clausifier_options                    --mode clausify
% 3.00/0.98  --stdin                                 false
% 3.00/0.98  --stats_out                             all
% 3.00/0.98  
% 3.00/0.98  ------ General Options
% 3.00/0.98  
% 3.00/0.98  --fof                                   false
% 3.00/0.98  --time_out_real                         305.
% 3.00/0.98  --time_out_virtual                      -1.
% 3.00/0.98  --symbol_type_check                     false
% 3.00/0.98  --clausify_out                          false
% 3.00/0.98  --sig_cnt_out                           false
% 3.00/0.98  --trig_cnt_out                          false
% 3.00/0.98  --trig_cnt_out_tolerance                1.
% 3.00/0.98  --trig_cnt_out_sk_spl                   false
% 3.00/0.98  --abstr_cl_out                          false
% 3.00/0.98  
% 3.00/0.98  ------ Global Options
% 3.00/0.98  
% 3.00/0.98  --schedule                              default
% 3.00/0.98  --add_important_lit                     false
% 3.00/0.98  --prop_solver_per_cl                    1000
% 3.00/0.98  --min_unsat_core                        false
% 3.00/0.98  --soft_assumptions                      false
% 3.00/0.98  --soft_lemma_size                       3
% 3.00/0.98  --prop_impl_unit_size                   0
% 3.00/0.98  --prop_impl_unit                        []
% 3.00/0.98  --share_sel_clauses                     true
% 3.00/0.98  --reset_solvers                         false
% 3.00/0.98  --bc_imp_inh                            [conj_cone]
% 3.00/0.98  --conj_cone_tolerance                   3.
% 3.00/0.98  --extra_neg_conj                        none
% 3.00/0.98  --large_theory_mode                     true
% 3.00/0.98  --prolific_symb_bound                   200
% 3.00/0.98  --lt_threshold                          2000
% 3.00/0.98  --clause_weak_htbl                      true
% 3.00/0.98  --gc_record_bc_elim                     false
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing Options
% 3.00/0.98  
% 3.00/0.98  --preprocessing_flag                    true
% 3.00/0.98  --time_out_prep_mult                    0.1
% 3.00/0.98  --splitting_mode                        input
% 3.00/0.98  --splitting_grd                         true
% 3.00/0.98  --splitting_cvd                         false
% 3.00/0.98  --splitting_cvd_svl                     false
% 3.00/0.98  --splitting_nvd                         32
% 3.00/0.98  --sub_typing                            true
% 3.00/0.98  --prep_gs_sim                           true
% 3.00/0.98  --prep_unflatten                        true
% 3.00/0.98  --prep_res_sim                          true
% 3.00/0.98  --prep_upred                            true
% 3.00/0.98  --prep_sem_filter                       exhaustive
% 3.00/0.98  --prep_sem_filter_out                   false
% 3.00/0.98  --pred_elim                             true
% 3.00/0.98  --res_sim_input                         true
% 3.00/0.98  --eq_ax_congr_red                       true
% 3.00/0.98  --pure_diseq_elim                       true
% 3.00/0.98  --brand_transform                       false
% 3.00/0.98  --non_eq_to_eq                          false
% 3.00/0.98  --prep_def_merge                        true
% 3.00/0.98  --prep_def_merge_prop_impl              false
% 3.00/0.98  --prep_def_merge_mbd                    true
% 3.00/0.98  --prep_def_merge_tr_red                 false
% 3.00/0.98  --prep_def_merge_tr_cl                  false
% 3.00/0.98  --smt_preprocessing                     true
% 3.00/0.98  --smt_ac_axioms                         fast
% 3.00/0.98  --preprocessed_out                      false
% 3.00/0.98  --preprocessed_stats                    false
% 3.00/0.98  
% 3.00/0.98  ------ Abstraction refinement Options
% 3.00/0.98  
% 3.00/0.98  --abstr_ref                             []
% 3.00/0.98  --abstr_ref_prep                        false
% 3.00/0.98  --abstr_ref_until_sat                   false
% 3.00/0.98  --abstr_ref_sig_restrict                funpre
% 3.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.98  --abstr_ref_under                       []
% 3.00/0.98  
% 3.00/0.98  ------ SAT Options
% 3.00/0.98  
% 3.00/0.98  --sat_mode                              false
% 3.00/0.98  --sat_fm_restart_options                ""
% 3.00/0.98  --sat_gr_def                            false
% 3.00/0.98  --sat_epr_types                         true
% 3.00/0.98  --sat_non_cyclic_types                  false
% 3.00/0.98  --sat_finite_models                     false
% 3.00/0.98  --sat_fm_lemmas                         false
% 3.00/0.98  --sat_fm_prep                           false
% 3.00/0.98  --sat_fm_uc_incr                        true
% 3.00/0.98  --sat_out_model                         small
% 3.00/0.98  --sat_out_clauses                       false
% 3.00/0.98  
% 3.00/0.98  ------ QBF Options
% 3.00/0.98  
% 3.00/0.98  --qbf_mode                              false
% 3.00/0.98  --qbf_elim_univ                         false
% 3.00/0.98  --qbf_dom_inst                          none
% 3.00/0.98  --qbf_dom_pre_inst                      false
% 3.00/0.98  --qbf_sk_in                             false
% 3.00/0.98  --qbf_pred_elim                         true
% 3.00/0.98  --qbf_split                             512
% 3.00/0.98  
% 3.00/0.98  ------ BMC1 Options
% 3.00/0.98  
% 3.00/0.98  --bmc1_incremental                      false
% 3.00/0.98  --bmc1_axioms                           reachable_all
% 3.00/0.98  --bmc1_min_bound                        0
% 3.00/0.98  --bmc1_max_bound                        -1
% 3.00/0.98  --bmc1_max_bound_default                -1
% 3.00/0.98  --bmc1_symbol_reachability              true
% 3.00/0.98  --bmc1_property_lemmas                  false
% 3.00/0.98  --bmc1_k_induction                      false
% 3.00/0.98  --bmc1_non_equiv_states                 false
% 3.00/0.98  --bmc1_deadlock                         false
% 3.00/0.98  --bmc1_ucm                              false
% 3.00/0.98  --bmc1_add_unsat_core                   none
% 3.00/0.98  --bmc1_unsat_core_children              false
% 3.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.98  --bmc1_out_stat                         full
% 3.00/0.98  --bmc1_ground_init                      false
% 3.00/0.98  --bmc1_pre_inst_next_state              false
% 3.00/0.98  --bmc1_pre_inst_state                   false
% 3.00/0.98  --bmc1_pre_inst_reach_state             false
% 3.00/0.98  --bmc1_out_unsat_core                   false
% 3.00/0.98  --bmc1_aig_witness_out                  false
% 3.00/0.98  --bmc1_verbose                          false
% 3.00/0.98  --bmc1_dump_clauses_tptp                false
% 3.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.98  --bmc1_dump_file                        -
% 3.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.98  --bmc1_ucm_extend_mode                  1
% 3.00/0.98  --bmc1_ucm_init_mode                    2
% 3.00/0.98  --bmc1_ucm_cone_mode                    none
% 3.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.98  --bmc1_ucm_relax_model                  4
% 3.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.98  --bmc1_ucm_layered_model                none
% 3.00/0.98  --bmc1_ucm_max_lemma_size               10
% 3.00/0.98  
% 3.00/0.98  ------ AIG Options
% 3.00/0.98  
% 3.00/0.98  --aig_mode                              false
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation Options
% 3.00/0.98  
% 3.00/0.98  --instantiation_flag                    true
% 3.00/0.98  --inst_sos_flag                         false
% 3.00/0.98  --inst_sos_phase                        true
% 3.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel_side                     none
% 3.00/0.98  --inst_solver_per_active                1400
% 3.00/0.98  --inst_solver_calls_frac                1.
% 3.00/0.98  --inst_passive_queue_type               priority_queues
% 3.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.98  --inst_passive_queues_freq              [25;2]
% 3.00/0.98  --inst_dismatching                      true
% 3.00/0.98  --inst_eager_unprocessed_to_passive     true
% 3.00/0.98  --inst_prop_sim_given                   true
% 3.00/0.98  --inst_prop_sim_new                     false
% 3.00/0.98  --inst_subs_new                         false
% 3.00/0.98  --inst_eq_res_simp                      false
% 3.00/0.98  --inst_subs_given                       false
% 3.00/0.98  --inst_orphan_elimination               true
% 3.00/0.98  --inst_learning_loop_flag               true
% 3.00/0.98  --inst_learning_start                   3000
% 3.00/0.98  --inst_learning_factor                  2
% 3.00/0.98  --inst_start_prop_sim_after_learn       3
% 3.00/0.98  --inst_sel_renew                        solver
% 3.00/0.98  --inst_lit_activity_flag                true
% 3.00/0.98  --inst_restr_to_given                   false
% 3.00/0.98  --inst_activity_threshold               500
% 3.00/0.98  --inst_out_proof                        true
% 3.00/0.98  
% 3.00/0.98  ------ Resolution Options
% 3.00/0.98  
% 3.00/0.98  --resolution_flag                       false
% 3.00/0.98  --res_lit_sel                           adaptive
% 3.00/0.98  --res_lit_sel_side                      none
% 3.00/0.98  --res_ordering                          kbo
% 3.00/0.98  --res_to_prop_solver                    active
% 3.00/0.98  --res_prop_simpl_new                    false
% 3.00/0.98  --res_prop_simpl_given                  true
% 3.00/0.98  --res_passive_queue_type                priority_queues
% 3.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.98  --res_passive_queues_freq               [15;5]
% 3.00/0.98  --res_forward_subs                      full
% 3.00/0.98  --res_backward_subs                     full
% 3.00/0.98  --res_forward_subs_resolution           true
% 3.00/0.98  --res_backward_subs_resolution          true
% 3.00/0.98  --res_orphan_elimination                true
% 3.00/0.98  --res_time_limit                        2.
% 3.00/0.98  --res_out_proof                         true
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Options
% 3.00/0.98  
% 3.00/0.98  --superposition_flag                    true
% 3.00/0.98  --sup_passive_queue_type                priority_queues
% 3.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.98  --demod_completeness_check              fast
% 3.00/0.98  --demod_use_ground                      true
% 3.00/0.98  --sup_to_prop_solver                    passive
% 3.00/0.98  --sup_prop_simpl_new                    true
% 3.00/0.98  --sup_prop_simpl_given                  true
% 3.00/0.98  --sup_fun_splitting                     false
% 3.00/0.98  --sup_smt_interval                      50000
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Simplification Setup
% 3.00/0.98  
% 3.00/0.98  --sup_indices_passive                   []
% 3.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_full_bw                           [BwDemod]
% 3.00/0.98  --sup_immed_triv                        [TrivRules]
% 3.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_immed_bw_main                     []
% 3.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  
% 3.00/0.98  ------ Combination Options
% 3.00/0.98  
% 3.00/0.98  --comb_res_mult                         3
% 3.00/0.98  --comb_sup_mult                         2
% 3.00/0.98  --comb_inst_mult                        10
% 3.00/0.98  
% 3.00/0.98  ------ Debug Options
% 3.00/0.98  
% 3.00/0.98  --dbg_backtrace                         false
% 3.00/0.98  --dbg_dump_prop_clauses                 false
% 3.00/0.98  --dbg_dump_prop_clauses_file            -
% 3.00/0.98  --dbg_out_stat                          false
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  ------ Proving...
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  % SZS status Theorem for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  fof(f2,axiom,(
% 3.00/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f19,plain,(
% 3.00/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f2])).
% 3.00/0.98  
% 3.00/0.98  fof(f41,plain,(
% 3.00/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f19])).
% 3.00/0.98  
% 3.00/0.98  fof(f16,conjecture,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f17,negated_conjecture,(
% 3.00/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.00/0.98    inference(negated_conjecture,[],[f16])).
% 3.00/0.98  
% 3.00/0.98  fof(f32,plain,(
% 3.00/0.98    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.00/0.98    inference(ennf_transformation,[],[f17])).
% 3.00/0.98  
% 3.00/0.98  fof(f36,plain,(
% 3.00/0.98    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f37,plain,(
% 3.00/0.98    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f36])).
% 3.00/0.98  
% 3.00/0.98  fof(f58,plain,(
% 3.00/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.00/0.98    inference(cnf_transformation,[],[f37])).
% 3.00/0.98  
% 3.00/0.98  fof(f5,axiom,(
% 3.00/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f45,plain,(
% 3.00/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f5])).
% 3.00/0.98  
% 3.00/0.98  fof(f1,axiom,(
% 3.00/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f33,plain,(
% 3.00/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.98    inference(nnf_transformation,[],[f1])).
% 3.00/0.98  
% 3.00/0.98  fof(f34,plain,(
% 3.00/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.98    inference(flattening,[],[f33])).
% 3.00/0.98  
% 3.00/0.98  fof(f39,plain,(
% 3.00/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.00/0.98    inference(cnf_transformation,[],[f34])).
% 3.00/0.98  
% 3.00/0.98  fof(f60,plain,(
% 3.00/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.00/0.98    inference(equality_resolution,[],[f39])).
% 3.00/0.98  
% 3.00/0.98  fof(f9,axiom,(
% 3.00/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f23,plain,(
% 3.00/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(ennf_transformation,[],[f9])).
% 3.00/0.98  
% 3.00/0.98  fof(f24,plain,(
% 3.00/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(flattening,[],[f23])).
% 3.00/0.98  
% 3.00/0.98  fof(f50,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f24])).
% 3.00/0.98  
% 3.00/0.98  fof(f4,axiom,(
% 3.00/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f44,plain,(
% 3.00/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f4])).
% 3.00/0.98  
% 3.00/0.98  fof(f7,axiom,(
% 3.00/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f22,plain,(
% 3.00/0.98    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f7])).
% 3.00/0.98  
% 3.00/0.98  fof(f47,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f22])).
% 3.00/0.98  
% 3.00/0.98  fof(f8,axiom,(
% 3.00/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f48,plain,(
% 3.00/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.00/0.98    inference(cnf_transformation,[],[f8])).
% 3.00/0.98  
% 3.00/0.98  fof(f11,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f18,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.00/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.00/0.98  
% 3.00/0.98  fof(f27,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f18])).
% 3.00/0.98  
% 3.00/0.98  fof(f52,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f27])).
% 3.00/0.98  
% 3.00/0.98  fof(f3,axiom,(
% 3.00/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f20,plain,(
% 3.00/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(ennf_transformation,[],[f3])).
% 3.00/0.98  
% 3.00/0.98  fof(f35,plain,(
% 3.00/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(nnf_transformation,[],[f20])).
% 3.00/0.98  
% 3.00/0.98  fof(f42,plain,(
% 3.00/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f35])).
% 3.00/0.98  
% 3.00/0.98  fof(f10,axiom,(
% 3.00/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f25,plain,(
% 3.00/0.98    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(ennf_transformation,[],[f10])).
% 3.00/0.98  
% 3.00/0.98  fof(f26,plain,(
% 3.00/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(flattening,[],[f25])).
% 3.00/0.98  
% 3.00/0.98  fof(f51,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f26])).
% 3.00/0.98  
% 3.00/0.98  fof(f6,axiom,(
% 3.00/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f21,plain,(
% 3.00/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(ennf_transformation,[],[f6])).
% 3.00/0.98  
% 3.00/0.98  fof(f46,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f21])).
% 3.00/0.98  
% 3.00/0.98  fof(f14,axiom,(
% 3.00/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f30,plain,(
% 3.00/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f14])).
% 3.00/0.98  
% 3.00/0.98  fof(f55,plain,(
% 3.00/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f30])).
% 3.00/0.98  
% 3.00/0.98  fof(f12,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f28,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f12])).
% 3.00/0.98  
% 3.00/0.98  fof(f53,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f28])).
% 3.00/0.98  
% 3.00/0.98  fof(f59,plain,(
% 3.00/0.98    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 3.00/0.98    inference(cnf_transformation,[],[f37])).
% 3.00/0.98  
% 3.00/0.98  fof(f15,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f31,plain,(
% 3.00/0.98    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f15])).
% 3.00/0.98  
% 3.00/0.98  fof(f56,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f31])).
% 3.00/0.98  
% 3.00/0.98  fof(f57,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f31])).
% 3.00/0.98  
% 3.00/0.98  fof(f13,axiom,(
% 3.00/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f29,plain,(
% 3.00/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f13])).
% 3.00/0.98  
% 3.00/0.98  fof(f54,plain,(
% 3.00/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f29])).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/0.98      | ~ v1_relat_1(X1)
% 3.00/0.98      | v1_relat_1(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_21,negated_conjecture,
% 3.00/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.00/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_246,plain,
% 3.00/0.98      ( ~ v1_relat_1(X0)
% 3.00/0.98      | v1_relat_1(X1)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 3.00/0.98      | sK2 != X1 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_247,plain,
% 3.00/0.98      ( ~ v1_relat_1(X0)
% 3.00/0.98      | v1_relat_1(sK2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_246]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_616,plain,
% 3.00/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 3.00/0.98      | v1_relat_1(X0) != iProver_top
% 3.00/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_417,plain,( X0 = X0 ),theory(equality) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_731,plain,
% 3.00/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_417]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_721,plain,
% 3.00/0.98      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.00/0.98      | v1_relat_1(sK2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_247]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_867,plain,
% 3.00/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | v1_relat_1(sK2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_721]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_868,plain,
% 3.00/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.00/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_7,plain,
% 3.00/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_942,plain,
% 3.00/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_943,plain,
% 3.00/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1251,plain,
% 3.00/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_616,c_731,c_868,c_943]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1,plain,
% 3.00/0.98      ( r1_tarski(X0,X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_623,plain,
% 3.00/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_12,plain,
% 3.00/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.00/0.98      | ~ v1_relat_1(X0)
% 3.00/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.00/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_618,plain,
% 3.00/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 3.00/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1658,plain,
% 3.00/0.98      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_623,c_618]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4280,plain,
% 3.00/0.98      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1251,c_1658]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_6,plain,
% 3.00/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_622,plain,
% 3.00/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_9,plain,
% 3.00/0.98      ( ~ v1_relat_1(X0)
% 3.00/0.98      | ~ v1_relat_1(X1)
% 3.00/0.98      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_619,plain,
% 3.00/0.98      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.00/0.98      | v1_relat_1(X0) != iProver_top
% 3.00/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2574,plain,
% 3.00/0.98      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 3.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1251,c_619]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2848,plain,
% 3.00/0.98      ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_622,c_2574]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_11,plain,
% 3.00/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.00/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2856,plain,
% 3.00/0.98      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 3.00/0.98      inference(light_normalisation,[status(thm)],[c_2848,c_11]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4290,plain,
% 3.00/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_4280,c_2856]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_14,plain,
% 3.00/0.98      ( v5_relat_1(X0,X1)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.00/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_5,plain,
% 3.00/0.98      ( ~ v5_relat_1(X0,X1)
% 3.00/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.00/0.98      | ~ v1_relat_1(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_227,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.00/0.98      | ~ v1_relat_1(X0) ),
% 3.00/0.98      inference(resolution,[status(thm)],[c_14,c_5]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_261,plain,
% 3.00/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 3.00/0.98      | ~ v1_relat_1(X0)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | sK2 != X0 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_227,c_21]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_262,plain,
% 3.00/0.98      ( r1_tarski(k2_relat_1(sK2),X0)
% 3.00/0.98      | ~ v1_relat_1(sK2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_261]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_615,plain,
% 3.00/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 3.00/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_926,plain,
% 3.00/0.98      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
% 3.00/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.00/0.98      inference(equality_resolution,[status(thm)],[c_615]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1362,plain,
% 3.00/0.98      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_926,c_731,c_868,c_943]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1659,plain,
% 3.00/0.98      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
% 3.00/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1362,c_618]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_927,plain,
% 3.00/0.98      ( r1_tarski(k2_relat_1(sK2),sK0) | ~ v1_relat_1(sK2) ),
% 3.00/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_926]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1282,plain,
% 3.00/0.98      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 3.00/0.98      | ~ v1_relat_1(sK2)
% 3.00/0.98      | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1295,plain,
% 3.00/0.98      ( ~ r1_tarski(k2_relat_1(sK2),sK0)
% 3.00/0.98      | ~ v1_relat_1(sK2)
% 3.00/0.98      | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_1282]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2186,plain,
% 3.00/0.98      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_1659,c_731,c_867,c_927,c_942,c_1295]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_13,plain,
% 3.00/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.00/0.98      | ~ v1_relat_1(X0)
% 3.00/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.00/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_617,plain,
% 3.00/0.98      ( k7_relat_1(X0,X1) = X0
% 3.00/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3170,plain,
% 3.00/0.98      ( k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k5_relat_1(sK2,k6_relat_1(X0))
% 3.00/0.98      | r1_tarski(k10_relat_1(sK2,X0),X1) != iProver_top
% 3.00/0.98      | v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2856,c_617]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3620,plain,
% 3.00/0.98      ( k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),k10_relat_1(sK2,X0)) = k5_relat_1(sK2,k6_relat_1(X0))
% 3.00/0.98      | v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_623,c_3170]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4073,plain,
% 3.00/0.98      ( k7_relat_1(k5_relat_1(sK2,k6_relat_1(sK0)),k10_relat_1(sK2,sK0)) = k5_relat_1(sK2,k6_relat_1(sK0))
% 3.00/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2186,c_3620]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3169,plain,
% 3.00/0.98      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2186,c_2856]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4074,plain,
% 3.00/0.98      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2
% 3.00/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.00/0.98      inference(light_normalisation,[status(thm)],[c_4073,c_2186,c_3169]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1281,plain,
% 3.00/0.98      ( ~ r1_tarski(k1_relat_1(sK2),X0)
% 3.00/0.98      | ~ v1_relat_1(sK2)
% 3.00/0.98      | k7_relat_1(sK2,X0) = sK2 ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2669,plain,
% 3.00/0.98      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
% 3.00/0.98      | ~ v1_relat_1(sK2)
% 3.00/0.98      | k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_1281]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2670,plain,
% 3.00/0.98      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4077,plain,
% 3.00/0.98      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_4074,c_731,c_867,c_942,c_2669,c_2670]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_8,plain,
% 3.00/0.98      ( ~ v1_relat_1(X0)
% 3.00/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_620,plain,
% 3.00/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1504,plain,
% 3.00/0.98      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1251,c_620]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4081,plain,
% 3.00/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_4077,c_1504]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_17,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.00/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_294,plain,
% 3.00/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | sK2 != X2 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_295,plain,
% 3.00/0.98      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_294]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_771,plain,
% 3.00/0.98      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.00/0.98      inference(equality_resolution,[status(thm)],[c_295]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_15,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_312,plain,
% 3.00/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | sK2 != X2 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_313,plain,
% 3.00/0.98      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_312]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_730,plain,
% 3.00/0.98      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 3.00/0.98      inference(equality_resolution,[status(thm)],[c_313]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_20,negated_conjecture,
% 3.00/0.98      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 3.00/0.98      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_844,plain,
% 3.00/0.98      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 3.00/0.98      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_730,c_20]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1108,plain,
% 3.00/0.98      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 3.00/0.98      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_771,c_844]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1109,plain,
% 3.00/0.98      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 3.00/0.98      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_1108,c_771]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_19,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_276,plain,
% 3.00/0.98      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | sK2 != X2 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_277,plain,
% 3.00/0.98      ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_276]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_808,plain,
% 3.00/0.98      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
% 3.00/0.98      inference(equality_resolution,[status(thm)],[c_277]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1170,plain,
% 3.00/0.98      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
% 3.00/0.98      inference(light_normalisation,[status(thm)],[c_808,c_730]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_18,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_285,plain,
% 3.00/0.98      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | sK2 != X2 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_286,plain,
% 3.00/0.98      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_285]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_811,plain,
% 3.00/0.98      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
% 3.00/0.98      inference(equality_resolution,[status(thm)],[c_286]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1248,plain,
% 3.00/0.98      ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_811,c_771]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1415,plain,
% 3.00/0.98      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 3.00/0.98      | k10_relat_1(sK2,k2_relat_1(sK2)) != k10_relat_1(sK2,sK0) ),
% 3.00/0.98      inference(light_normalisation,[status(thm)],[c_1109,c_1170,c_1248]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_16,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.00/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_303,plain,
% 3.00/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.00/0.98      | sK2 != X2 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_304,plain,
% 3.00/0.98      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 3.00/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_303]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_775,plain,
% 3.00/0.98      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.00/0.98      inference(equality_resolution,[status(thm)],[c_304]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1416,plain,
% 3.00/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k10_relat_1(sK2,sK0)
% 3.00/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_1415,c_775]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3183,plain,
% 3.00/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 3.00/0.98      | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_3169,c_1416]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(contradiction,plain,
% 3.00/0.98      ( $false ),
% 3.00/0.98      inference(minisat,[status(thm)],[c_4290,c_4081,c_3183]) ).
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  ------                               Statistics
% 3.00/0.98  
% 3.00/0.98  ------ General
% 3.00/0.98  
% 3.00/0.98  abstr_ref_over_cycles:                  0
% 3.00/0.98  abstr_ref_under_cycles:                 0
% 3.00/0.98  gc_basic_clause_elim:                   0
% 3.00/0.98  forced_gc_time:                         0
% 3.00/0.98  parsing_time:                           0.008
% 3.00/0.98  unif_index_cands_time:                  0.
% 3.00/0.98  unif_index_add_time:                    0.
% 3.00/0.98  orderings_time:                         0.
% 3.00/0.98  out_proof_time:                         0.012
% 3.00/0.98  total_time:                             0.184
% 3.00/0.98  num_of_symbols:                         51
% 3.00/0.98  num_of_terms:                           5283
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing
% 3.00/0.98  
% 3.00/0.98  num_of_splits:                          0
% 3.00/0.98  num_of_split_atoms:                     0
% 3.00/0.98  num_of_reused_defs:                     0
% 3.00/0.98  num_eq_ax_congr_red:                    22
% 3.00/0.98  num_of_sem_filtered_clauses:            1
% 3.00/0.98  num_of_subtypes:                        0
% 3.00/0.98  monotx_restored_types:                  0
% 3.00/0.98  sat_num_of_epr_types:                   0
% 3.00/0.98  sat_num_of_non_cyclic_types:            0
% 3.00/0.98  sat_guarded_non_collapsed_types:        0
% 3.00/0.98  num_pure_diseq_elim:                    0
% 3.00/0.98  simp_replaced_by:                       0
% 3.00/0.98  res_preprocessed:                       106
% 3.00/0.98  prep_upred:                             0
% 3.00/0.98  prep_unflattend:                        7
% 3.00/0.98  smt_new_axioms:                         0
% 3.00/0.98  pred_elim_cands:                        2
% 3.00/0.98  pred_elim:                              2
% 3.00/0.98  pred_elim_cl:                           3
% 3.00/0.98  pred_elim_cycles:                       4
% 3.00/0.98  merged_defs:                            0
% 3.00/0.98  merged_defs_ncl:                        0
% 3.00/0.98  bin_hyper_res:                          0
% 3.00/0.98  prep_cycles:                            4
% 3.00/0.98  pred_elim_time:                         0.003
% 3.00/0.98  splitting_time:                         0.
% 3.00/0.98  sem_filter_time:                        0.
% 3.00/0.98  monotx_time:                            0.
% 3.00/0.98  subtype_inf_time:                       0.
% 3.00/0.98  
% 3.00/0.98  ------ Problem properties
% 3.00/0.98  
% 3.00/0.98  clauses:                                18
% 3.00/0.98  conjectures:                            1
% 3.00/0.98  epr:                                    2
% 3.00/0.98  horn:                                   18
% 3.00/0.98  ground:                                 1
% 3.00/0.98  unary:                                  5
% 3.00/0.98  binary:                                 7
% 3.00/0.98  lits:                                   37
% 3.00/0.98  lits_eq:                                21
% 3.00/0.98  fd_pure:                                0
% 3.00/0.98  fd_pseudo:                              0
% 3.00/0.98  fd_cond:                                0
% 3.00/0.98  fd_pseudo_cond:                         1
% 3.00/0.98  ac_symbols:                             0
% 3.00/0.98  
% 3.00/0.98  ------ Propositional Solver
% 3.00/0.98  
% 3.00/0.98  prop_solver_calls:                      28
% 3.00/0.98  prop_fast_solver_calls:                 636
% 3.00/0.98  smt_solver_calls:                       0
% 3.00/0.98  smt_fast_solver_calls:                  0
% 3.00/0.98  prop_num_of_clauses:                    1905
% 3.00/0.98  prop_preprocess_simplified:             5750
% 3.00/0.98  prop_fo_subsumed:                       7
% 3.00/0.98  prop_solver_time:                       0.
% 3.00/0.98  smt_solver_time:                        0.
% 3.00/0.98  smt_fast_solver_time:                   0.
% 3.00/0.98  prop_fast_solver_time:                  0.
% 3.00/0.98  prop_unsat_core_time:                   0.
% 3.00/0.98  
% 3.00/0.98  ------ QBF
% 3.00/0.98  
% 3.00/0.98  qbf_q_res:                              0
% 3.00/0.98  qbf_num_tautologies:                    0
% 3.00/0.98  qbf_prep_cycles:                        0
% 3.00/0.98  
% 3.00/0.98  ------ BMC1
% 3.00/0.98  
% 3.00/0.98  bmc1_current_bound:                     -1
% 3.00/0.98  bmc1_last_solved_bound:                 -1
% 3.00/0.98  bmc1_unsat_core_size:                   -1
% 3.00/0.98  bmc1_unsat_core_parents_size:           -1
% 3.00/0.98  bmc1_merge_next_fun:                    0
% 3.00/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation
% 3.00/0.98  
% 3.00/0.98  inst_num_of_clauses:                    612
% 3.00/0.98  inst_num_in_passive:                    264
% 3.00/0.98  inst_num_in_active:                     324
% 3.00/0.98  inst_num_in_unprocessed:                24
% 3.00/0.98  inst_num_of_loops:                      330
% 3.00/0.98  inst_num_of_learning_restarts:          0
% 3.00/0.98  inst_num_moves_active_passive:          4
% 3.00/0.98  inst_lit_activity:                      0
% 3.00/0.98  inst_lit_activity_moves:                0
% 3.00/0.98  inst_num_tautologies:                   0
% 3.00/0.98  inst_num_prop_implied:                  0
% 3.00/0.98  inst_num_existing_simplified:           0
% 3.00/0.98  inst_num_eq_res_simplified:             0
% 3.00/0.98  inst_num_child_elim:                    0
% 3.00/0.98  inst_num_of_dismatching_blockings:      125
% 3.00/0.98  inst_num_of_non_proper_insts:           559
% 3.00/0.98  inst_num_of_duplicates:                 0
% 3.00/0.98  inst_inst_num_from_inst_to_res:         0
% 3.00/0.98  inst_dismatching_checking_time:         0.
% 3.00/0.98  
% 3.00/0.98  ------ Resolution
% 3.00/0.98  
% 3.00/0.98  res_num_of_clauses:                     0
% 3.00/0.98  res_num_in_passive:                     0
% 3.00/0.98  res_num_in_active:                      0
% 3.00/0.98  res_num_of_loops:                       110
% 3.00/0.98  res_forward_subset_subsumed:            72
% 3.00/0.98  res_backward_subset_subsumed:           0
% 3.00/0.98  res_forward_subsumed:                   0
% 3.00/0.98  res_backward_subsumed:                  0
% 3.00/0.98  res_forward_subsumption_resolution:     0
% 3.00/0.98  res_backward_subsumption_resolution:    0
% 3.00/0.98  res_clause_to_clause_subsumption:       138
% 3.00/0.98  res_orphan_elimination:                 0
% 3.00/0.98  res_tautology_del:                      48
% 3.00/0.98  res_num_eq_res_simplified:              0
% 3.00/0.98  res_num_sel_changes:                    0
% 3.00/0.98  res_moves_from_active_to_pass:          0
% 3.00/0.98  
% 3.00/0.98  ------ Superposition
% 3.00/0.98  
% 3.00/0.98  sup_time_total:                         0.
% 3.00/0.98  sup_time_generating:                    0.
% 3.00/0.98  sup_time_sim_full:                      0.
% 3.00/0.98  sup_time_sim_immed:                     0.
% 3.00/0.98  
% 3.00/0.98  sup_num_of_clauses:                     72
% 3.00/0.98  sup_num_in_active:                      62
% 3.00/0.98  sup_num_in_passive:                     10
% 3.00/0.98  sup_num_of_loops:                       65
% 3.00/0.98  sup_fw_superposition:                   45
% 3.00/0.98  sup_bw_superposition:                   11
% 3.00/0.98  sup_immediate_simplified:               12
% 3.00/0.98  sup_given_eliminated:                   0
% 3.00/0.98  comparisons_done:                       0
% 3.00/0.98  comparisons_avoided:                    0
% 3.00/0.98  
% 3.00/0.98  ------ Simplifications
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  sim_fw_subset_subsumed:                 0
% 3.00/0.98  sim_bw_subset_subsumed:                 1
% 3.00/0.98  sim_fw_subsumed:                        1
% 3.00/0.98  sim_bw_subsumed:                        0
% 3.00/0.98  sim_fw_subsumption_res:                 0
% 3.00/0.98  sim_bw_subsumption_res:                 0
% 3.00/0.98  sim_tautology_del:                      0
% 3.00/0.98  sim_eq_tautology_del:                   4
% 3.00/0.98  sim_eq_res_simp:                        0
% 3.00/0.98  sim_fw_demodulated:                     6
% 3.00/0.98  sim_bw_demodulated:                     4
% 3.00/0.98  sim_light_normalised:                   10
% 3.00/0.98  sim_joinable_taut:                      0
% 3.00/0.98  sim_joinable_simp:                      0
% 3.00/0.98  sim_ac_normalised:                      0
% 3.00/0.98  sim_smt_subsumption:                    0
% 3.00/0.98  
%------------------------------------------------------------------------------
