%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:07 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 589 expanded)
%              Number of clauses        :   92 ( 250 expanded)
%              Number of leaves         :   18 ( 117 expanded)
%              Depth                    :   18
%              Number of atoms          :  338 (1437 expanded)
%              Number of equality atoms :  181 ( 745 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f37])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_344,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_345,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_721,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_513,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_832,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_917,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_918,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_1373,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_832,c_918])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_727,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_375,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_10])).

cnf(c_720,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_4208,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_720])).

cnf(c_4685,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1373,c_4208])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_725,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1694,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1373,c_725])).

cnf(c_4835,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4685,c_1694])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_332,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_333,plain,
    ( v4_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_390,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_333])).

cnf(c_391,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_395,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_345])).

cnf(c_1022,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_395])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_723,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1956,plain,
    ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k7_relat_1(sK2,X0)
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1694,c_723])).

cnf(c_2630,plain,
    ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(k9_relat_1(sK2,X0))) = k7_relat_1(sK2,X0)
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_1956])).

cnf(c_3106,plain,
    ( k5_relat_1(k7_relat_1(sK2,sK1),k6_relat_1(k9_relat_1(sK2,sK1))) = k7_relat_1(sK2,sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_2630])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_314,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_315,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_855,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_315])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_287,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_288,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_884,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_288])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_323,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_324,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_831,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_324])).

cnf(c_1255,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_884,c_831])).

cnf(c_1257,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_855,c_1255])).

cnf(c_3107,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3106,c_1022,c_1257])).

cnf(c_3110,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3107,c_832,c_918])).

cnf(c_7,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_726,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_724,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1803,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_724])).

cnf(c_2219,plain,
    ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_726,c_1803])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2224,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2219,c_12])).

cnf(c_3113,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3110,c_2224])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_259,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_14])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_259])).

cnf(c_275,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_260,c_23])).

cnf(c_276,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_722,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_1415,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_722])).

cnf(c_1943,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1415,c_723])).

cnf(c_833,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_988,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1000,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_2555,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1943,c_832,c_833,c_917,c_1000])).

cnf(c_2644,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2555,c_2224])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_305,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_306,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_851,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_306])).

cnf(c_22,negated_conjecture,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_923,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_831,c_22])).

cnf(c_1164,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_851,c_923])).

cnf(c_1165,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1164,c_851])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_296,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_297,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_887,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_297])).

cnf(c_1370,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_887,c_851])).

cnf(c_2479,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k2_relat_1(sK2)) != k10_relat_1(sK2,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1165,c_1255,c_1370])).

cnf(c_2480,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k10_relat_1(sK2,sK0)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2479,c_855])).

cnf(c_2739,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2644,c_2480])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4835,c_3113,c_2739])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:16:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.73/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/0.99  
% 2.73/0.99  ------  iProver source info
% 2.73/0.99  
% 2.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/0.99  git: non_committed_changes: false
% 2.73/0.99  git: last_make_outside_of_git: false
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     num_symb
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       true
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  ------ Parsing...
% 2.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/0.99  ------ Proving...
% 2.73/0.99  ------ Problem Properties 
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  clauses                                 19
% 2.73/0.99  conjectures                             1
% 2.73/0.99  EPR                                     2
% 2.73/0.99  Horn                                    19
% 2.73/0.99  unary                                   4
% 2.73/0.99  binary                                  11
% 2.73/0.99  lits                                    38
% 2.73/0.99  lits eq                                 24
% 2.73/0.99  fd_pure                                 0
% 2.73/0.99  fd_pseudo                               0
% 2.73/0.99  fd_cond                                 0
% 2.73/0.99  fd_pseudo_cond                          1
% 2.73/0.99  AC symbols                              0
% 2.73/0.99  
% 2.73/0.99  ------ Schedule dynamic 5 is on 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  Current options:
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     none
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       false
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ Proving...
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  % SZS status Theorem for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  fof(f10,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f26,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f10])).
% 2.73/0.99  
% 2.73/0.99  fof(f53,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f26])).
% 2.73/0.99  
% 2.73/0.99  fof(f16,conjecture,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f17,negated_conjecture,(
% 2.73/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.73/0.99    inference(negated_conjecture,[],[f16])).
% 2.73/0.99  
% 2.73/0.99  fof(f32,plain,(
% 2.73/0.99    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.73/0.99    inference(ennf_transformation,[],[f17])).
% 2.73/0.99  
% 2.73/0.99  fof(f37,plain,(
% 2.73/0.99    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f38,plain,(
% 2.73/0.99    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f37])).
% 2.73/0.99  
% 2.73/0.99  fof(f61,plain,(
% 2.73/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.73/0.99    inference(cnf_transformation,[],[f38])).
% 2.73/0.99  
% 2.73/0.99  fof(f1,axiom,(
% 2.73/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f33,plain,(
% 2.73/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.73/0.99    inference(nnf_transformation,[],[f1])).
% 2.73/0.99  
% 2.73/0.99  fof(f34,plain,(
% 2.73/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.73/0.99    inference(flattening,[],[f33])).
% 2.73/0.99  
% 2.73/0.99  fof(f40,plain,(
% 2.73/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.73/0.99    inference(cnf_transformation,[],[f34])).
% 2.73/0.99  
% 2.73/0.99  fof(f63,plain,(
% 2.73/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.73/0.99    inference(equality_resolution,[],[f40])).
% 2.73/0.99  
% 2.73/0.99  fof(f2,axiom,(
% 2.73/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f18,plain,(
% 2.73/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.73/0.99    inference(ennf_transformation,[],[f2])).
% 2.73/0.99  
% 2.73/0.99  fof(f35,plain,(
% 2.73/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.73/0.99    inference(nnf_transformation,[],[f18])).
% 2.73/0.99  
% 2.73/0.99  fof(f43,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f35])).
% 2.73/0.99  
% 2.73/0.99  fof(f7,axiom,(
% 2.73/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f22,plain,(
% 2.73/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.73/0.99    inference(ennf_transformation,[],[f7])).
% 2.73/0.99  
% 2.73/0.99  fof(f23,plain,(
% 2.73/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.73/0.99    inference(flattening,[],[f22])).
% 2.73/0.99  
% 2.73/0.99  fof(f49,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f23])).
% 2.73/0.99  
% 2.73/0.99  fof(f5,axiom,(
% 2.73/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f20,plain,(
% 2.73/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.73/0.99    inference(ennf_transformation,[],[f5])).
% 2.73/0.99  
% 2.73/0.99  fof(f47,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f20])).
% 2.73/0.99  
% 2.73/0.99  fof(f11,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f27,plain,(
% 2.73/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f11])).
% 2.73/0.99  
% 2.73/0.99  fof(f54,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f9,axiom,(
% 2.73/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f24,plain,(
% 2.73/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.73/0.99    inference(ennf_transformation,[],[f9])).
% 2.73/0.99  
% 2.73/0.99  fof(f25,plain,(
% 2.73/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.73/0.99    inference(flattening,[],[f24])).
% 2.73/0.99  
% 2.73/0.99  fof(f52,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f13,axiom,(
% 2.73/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f29,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f13])).
% 2.73/0.99  
% 2.73/0.99  fof(f57,plain,(
% 2.73/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f29])).
% 2.73/0.99  
% 2.73/0.99  fof(f15,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f31,plain,(
% 2.73/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f15])).
% 2.73/0.99  
% 2.73/0.99  fof(f59,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f31])).
% 2.73/0.99  
% 2.73/0.99  fof(f12,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f28,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f12])).
% 2.73/0.99  
% 2.73/0.99  fof(f56,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f28])).
% 2.73/0.99  
% 2.73/0.99  fof(f4,axiom,(
% 2.73/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f46,plain,(
% 2.73/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f4])).
% 2.73/0.99  
% 2.73/0.99  fof(f6,axiom,(
% 2.73/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f21,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f6])).
% 2.73/0.99  
% 2.73/0.99  fof(f48,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f21])).
% 2.73/0.99  
% 2.73/0.99  fof(f8,axiom,(
% 2.73/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f50,plain,(
% 2.73/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.73/0.99    inference(cnf_transformation,[],[f8])).
% 2.73/0.99  
% 2.73/0.99  fof(f3,axiom,(
% 2.73/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f19,plain,(
% 2.73/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.73/0.99    inference(ennf_transformation,[],[f3])).
% 2.73/0.99  
% 2.73/0.99  fof(f36,plain,(
% 2.73/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.73/0.99    inference(nnf_transformation,[],[f19])).
% 2.73/0.99  
% 2.73/0.99  fof(f44,plain,(
% 2.73/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f36])).
% 2.73/0.99  
% 2.73/0.99  fof(f55,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f14,axiom,(
% 2.73/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f30,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f14])).
% 2.73/0.99  
% 2.73/0.99  fof(f58,plain,(
% 2.73/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f62,plain,(
% 2.73/0.99    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 2.73/0.99    inference(cnf_transformation,[],[f38])).
% 2.73/0.99  
% 2.73/0.99  fof(f60,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f31])).
% 2.73/0.99  
% 2.73/0.99  cnf(c_14,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | v1_relat_1(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_23,negated_conjecture,
% 2.73/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.73/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_344,plain,
% 2.73/0.99      ( v1_relat_1(X0)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/0.99      | sK2 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_345,plain,
% 2.73/0.99      ( v1_relat_1(sK2)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_721,plain,
% 2.73/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_513,plain,( X0 = X0 ),theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_832,plain,
% 2.73/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_513]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_917,plain,
% 2.73/0.99      ( v1_relat_1(sK2)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_345]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_918,plain,
% 2.73/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_917]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1373,plain,
% 2.73/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_721,c_832,c_918]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1,plain,
% 2.73/0.99      ( r1_tarski(X0,X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_727,plain,
% 2.73/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3,plain,
% 2.73/0.99      ( v4_relat_1(X0,X1)
% 2.73/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.73/0.99      | ~ v1_relat_1(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_10,plain,
% 2.73/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.73/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_375,plain,
% 2.73/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.73/0.99      | ~ v1_relat_1(X0)
% 2.73/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.73/0.99      inference(resolution,[status(thm)],[c_3,c_10]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_720,plain,
% 2.73/0.99      ( k7_relat_1(X0,X1) = X0
% 2.73/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.73/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4208,plain,
% 2.73/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.73/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_727,c_720]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4685,plain,
% 2.73/0.99      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1373,c_4208]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_8,plain,
% 2.73/0.99      ( ~ v1_relat_1(X0)
% 2.73/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_725,plain,
% 2.73/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.73/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1694,plain,
% 2.73/0.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1373,c_725]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4835,plain,
% 2.73/0.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_4685,c_1694]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_16,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | v4_relat_1(X0,X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_332,plain,
% 2.73/0.99      ( v4_relat_1(X0,X1)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/0.99      | sK2 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_333,plain,
% 2.73/0.99      ( v4_relat_1(sK2,X0)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_332]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_390,plain,
% 2.73/0.99      ( ~ v1_relat_1(X0)
% 2.73/0.99      | X1 != X2
% 2.73/0.99      | k7_relat_1(X0,X2) = X0
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/0.99      | sK2 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_333]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_391,plain,
% 2.73/0.99      ( ~ v1_relat_1(sK2)
% 2.73/0.99      | k7_relat_1(sK2,X0) = sK2
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_395,plain,
% 2.73/0.99      ( k7_relat_1(sK2,X0) = sK2
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_391,c_345]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1022,plain,
% 2.73/0.99      ( k7_relat_1(sK2,sK1) = sK2 ),
% 2.73/0.99      inference(equality_resolution,[status(thm)],[c_395]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_13,plain,
% 2.73/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.73/0.99      | ~ v1_relat_1(X0)
% 2.73/0.99      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.73/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_723,plain,
% 2.73/0.99      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.73/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.73/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1956,plain,
% 2.73/0.99      ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k7_relat_1(sK2,X0)
% 2.73/0.99      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 2.73/0.99      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1694,c_723]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2630,plain,
% 2.73/0.99      ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(k9_relat_1(sK2,X0))) = k7_relat_1(sK2,X0)
% 2.73/0.99      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_727,c_1956]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3106,plain,
% 2.73/0.99      ( k5_relat_1(k7_relat_1(sK2,sK1),k6_relat_1(k9_relat_1(sK2,sK1))) = k7_relat_1(sK2,sK1)
% 2.73/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1022,c_2630]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_18,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.73/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_314,plain,
% 2.73/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/0.99      | sK2 != X2 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_315,plain,
% 2.73/0.99      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_314]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_855,plain,
% 2.73/0.99      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.73/0.99      inference(equality_resolution,[status(thm)],[c_315]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_21,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_287,plain,
% 2.73/0.99      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/0.99      | sK2 != X2 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_288,plain,
% 2.73/0.99      ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_287]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_884,plain,
% 2.73/0.99      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
% 2.73/0.99      inference(equality_resolution,[status(thm)],[c_288]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_17,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_323,plain,
% 2.73/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/0.99      | sK2 != X2 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_324,plain,
% 2.73/0.99      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_323]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_831,plain,
% 2.73/0.99      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 2.73/1.00      inference(equality_resolution,[status(thm)],[c_324]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1255,plain,
% 2.73/1.00      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_884,c_831]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1257,plain,
% 2.73/1.00      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_855,c_1255]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3107,plain,
% 2.73/1.00      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2
% 2.73/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_3106,c_1022,c_1257]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3110,plain,
% 2.73/1.00      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_3107,c_832,c_918]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_7,plain,
% 2.73/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_726,plain,
% 2.73/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_9,plain,
% 2.73/1.00      ( ~ v1_relat_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X1)
% 2.73/1.00      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_724,plain,
% 2.73/1.00      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.73/1.00      | v1_relat_1(X1) != iProver_top
% 2.73/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1803,plain,
% 2.73/1.00      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 2.73/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1373,c_724]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2219,plain,
% 2.73/1.00      ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_726,c_1803]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_12,plain,
% 2.73/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2224,plain,
% 2.73/1.00      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_2219,c_12]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3113,plain,
% 2.73/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_3110,c_2224]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_6,plain,
% 2.73/1.00      ( ~ v5_relat_1(X0,X1)
% 2.73/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 2.73/1.00      | ~ v1_relat_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_15,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | v5_relat_1(X0,X2) ),
% 2.73/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_254,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | r1_tarski(k2_relat_1(X3),X4)
% 2.73/1.00      | ~ v1_relat_1(X3)
% 2.73/1.00      | X0 != X3
% 2.73/1.00      | X2 != X4 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_255,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 2.73/1.00      | ~ v1_relat_1(X0) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_254]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_259,plain,
% 2.73/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_255,c_14]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_260,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_259]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_275,plain,
% 2.73/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 2.73/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/1.00      | sK2 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_260,c_23]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_276,plain,
% 2.73/1.00      ( r1_tarski(k2_relat_1(sK2),X0)
% 2.73/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_275]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_722,plain,
% 2.73/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/1.00      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1415,plain,
% 2.73/1.00      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 2.73/1.00      inference(equality_resolution,[status(thm)],[c_722]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1943,plain,
% 2.73/1.00      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
% 2.73/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1415,c_723]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_833,plain,
% 2.73/1.00      ( r1_tarski(k2_relat_1(sK2),sK0)
% 2.73/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_276]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_988,plain,
% 2.73/1.00      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 2.73/1.00      | ~ v1_relat_1(sK2)
% 2.73/1.00      | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1000,plain,
% 2.73/1.00      ( ~ r1_tarski(k2_relat_1(sK2),sK0)
% 2.73/1.00      | ~ v1_relat_1(sK2)
% 2.73/1.00      | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_988]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2555,plain,
% 2.73/1.00      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1943,c_832,c_833,c_917,c_1000]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2644,plain,
% 2.73/1.00      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_2555,c_2224]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_19,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.73/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_305,plain,
% 2.73/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.73/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/1.00      | sK2 != X2 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_306,plain,
% 2.73/1.00      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.73/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_305]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_851,plain,
% 2.73/1.00      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.73/1.00      inference(equality_resolution,[status(thm)],[c_306]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_22,negated_conjecture,
% 2.73/1.00      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.73/1.00      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_923,plain,
% 2.73/1.00      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.73/1.00      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_831,c_22]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1164,plain,
% 2.73/1.00      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 2.73/1.00      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_851,c_923]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1165,plain,
% 2.73/1.00      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.73/1.00      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_1164,c_851]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_20,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_296,plain,
% 2.73/1.00      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.73/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.73/1.00      | sK2 != X2 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_297,plain,
% 2.73/1.00      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 2.73/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_296]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_887,plain,
% 2.73/1.00      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
% 2.73/1.00      inference(equality_resolution,[status(thm)],[c_297]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1370,plain,
% 2.73/1.00      ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_887,c_851]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2479,plain,
% 2.73/1.00      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.73/1.00      | k10_relat_1(sK2,k2_relat_1(sK2)) != k10_relat_1(sK2,sK0) ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_1165,c_1255,c_1370]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2480,plain,
% 2.73/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k10_relat_1(sK2,sK0)
% 2.73/1.00      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_2479,c_855]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2739,plain,
% 2.73/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.73/1.00      | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_2644,c_2480]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(contradiction,plain,
% 2.73/1.00      ( $false ),
% 2.73/1.00      inference(minisat,[status(thm)],[c_4835,c_3113,c_2739]) ).
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  ------                               Statistics
% 2.73/1.00  
% 2.73/1.00  ------ General
% 2.73/1.00  
% 2.73/1.00  abstr_ref_over_cycles:                  0
% 2.73/1.00  abstr_ref_under_cycles:                 0
% 2.73/1.00  gc_basic_clause_elim:                   0
% 2.73/1.00  forced_gc_time:                         0
% 2.73/1.00  parsing_time:                           0.009
% 2.73/1.00  unif_index_cands_time:                  0.
% 2.73/1.00  unif_index_add_time:                    0.
% 2.73/1.00  orderings_time:                         0.
% 2.73/1.00  out_proof_time:                         0.007
% 2.73/1.00  total_time:                             0.163
% 2.73/1.00  num_of_symbols:                         52
% 2.73/1.00  num_of_terms:                           6028
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing
% 2.73/1.00  
% 2.73/1.00  num_of_splits:                          0
% 2.73/1.00  num_of_split_atoms:                     0
% 2.73/1.00  num_of_reused_defs:                     0
% 2.73/1.00  num_eq_ax_congr_red:                    22
% 2.73/1.00  num_of_sem_filtered_clauses:            1
% 2.73/1.00  num_of_subtypes:                        0
% 2.73/1.00  monotx_restored_types:                  0
% 2.73/1.00  sat_num_of_epr_types:                   0
% 2.73/1.00  sat_num_of_non_cyclic_types:            0
% 2.73/1.00  sat_guarded_non_collapsed_types:        0
% 2.73/1.00  num_pure_diseq_elim:                    0
% 2.73/1.00  simp_replaced_by:                       0
% 2.73/1.00  res_preprocessed:                       113
% 2.73/1.00  prep_upred:                             0
% 2.73/1.00  prep_unflattend:                        14
% 2.73/1.00  smt_new_axioms:                         0
% 2.73/1.00  pred_elim_cands:                        2
% 2.73/1.00  pred_elim:                              3
% 2.73/1.00  pred_elim_cl:                           4
% 2.73/1.00  pred_elim_cycles:                       5
% 2.73/1.00  merged_defs:                            0
% 2.73/1.00  merged_defs_ncl:                        0
% 2.73/1.00  bin_hyper_res:                          0
% 2.73/1.00  prep_cycles:                            4
% 2.73/1.00  pred_elim_time:                         0.003
% 2.73/1.00  splitting_time:                         0.
% 2.73/1.00  sem_filter_time:                        0.
% 2.73/1.00  monotx_time:                            0.
% 2.73/1.00  subtype_inf_time:                       0.
% 2.73/1.00  
% 2.73/1.00  ------ Problem properties
% 2.73/1.00  
% 2.73/1.00  clauses:                                19
% 2.73/1.00  conjectures:                            1
% 2.73/1.00  epr:                                    2
% 2.73/1.00  horn:                                   19
% 2.73/1.00  ground:                                 1
% 2.73/1.00  unary:                                  4
% 2.73/1.00  binary:                                 11
% 2.73/1.00  lits:                                   38
% 2.73/1.00  lits_eq:                                24
% 2.73/1.00  fd_pure:                                0
% 2.73/1.00  fd_pseudo:                              0
% 2.73/1.00  fd_cond:                                0
% 2.73/1.00  fd_pseudo_cond:                         1
% 2.73/1.00  ac_symbols:                             0
% 2.73/1.00  
% 2.73/1.00  ------ Propositional Solver
% 2.73/1.00  
% 2.73/1.00  prop_solver_calls:                      28
% 2.73/1.00  prop_fast_solver_calls:                 664
% 2.73/1.00  smt_solver_calls:                       0
% 2.73/1.00  smt_fast_solver_calls:                  0
% 2.73/1.00  prop_num_of_clauses:                    2368
% 2.73/1.00  prop_preprocess_simplified:             6630
% 2.73/1.00  prop_fo_subsumed:                       8
% 2.73/1.00  prop_solver_time:                       0.
% 2.73/1.00  smt_solver_time:                        0.
% 2.73/1.00  smt_fast_solver_time:                   0.
% 2.73/1.00  prop_fast_solver_time:                  0.
% 2.73/1.00  prop_unsat_core_time:                   0.
% 2.73/1.00  
% 2.73/1.00  ------ QBF
% 2.73/1.00  
% 2.73/1.00  qbf_q_res:                              0
% 2.73/1.00  qbf_num_tautologies:                    0
% 2.73/1.00  qbf_prep_cycles:                        0
% 2.73/1.00  
% 2.73/1.00  ------ BMC1
% 2.73/1.00  
% 2.73/1.00  bmc1_current_bound:                     -1
% 2.73/1.00  bmc1_last_solved_bound:                 -1
% 2.73/1.00  bmc1_unsat_core_size:                   -1
% 2.73/1.00  bmc1_unsat_core_parents_size:           -1
% 2.73/1.00  bmc1_merge_next_fun:                    0
% 2.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation
% 2.73/1.00  
% 2.73/1.00  inst_num_of_clauses:                    752
% 2.73/1.00  inst_num_in_passive:                    324
% 2.73/1.00  inst_num_in_active:                     326
% 2.73/1.00  inst_num_in_unprocessed:                103
% 2.73/1.00  inst_num_of_loops:                      330
% 2.73/1.00  inst_num_of_learning_restarts:          0
% 2.73/1.00  inst_num_moves_active_passive:          2
% 2.73/1.00  inst_lit_activity:                      0
% 2.73/1.00  inst_lit_activity_moves:                0
% 2.73/1.00  inst_num_tautologies:                   0
% 2.73/1.00  inst_num_prop_implied:                  0
% 2.73/1.00  inst_num_existing_simplified:           0
% 2.73/1.00  inst_num_eq_res_simplified:             0
% 2.73/1.00  inst_num_child_elim:                    0
% 2.73/1.00  inst_num_of_dismatching_blockings:      27
% 2.73/1.00  inst_num_of_non_proper_insts:           504
% 2.73/1.00  inst_num_of_duplicates:                 0
% 2.73/1.00  inst_inst_num_from_inst_to_res:         0
% 2.73/1.00  inst_dismatching_checking_time:         0.
% 2.73/1.00  
% 2.73/1.00  ------ Resolution
% 2.73/1.00  
% 2.73/1.00  res_num_of_clauses:                     0
% 2.73/1.00  res_num_in_passive:                     0
% 2.73/1.00  res_num_in_active:                      0
% 2.73/1.00  res_num_of_loops:                       117
% 2.73/1.00  res_forward_subset_subsumed:            65
% 2.73/1.00  res_backward_subset_subsumed:           2
% 2.73/1.00  res_forward_subsumed:                   0
% 2.73/1.00  res_backward_subsumed:                  0
% 2.73/1.00  res_forward_subsumption_resolution:     0
% 2.73/1.00  res_backward_subsumption_resolution:    0
% 2.73/1.00  res_clause_to_clause_subsumption:       134
% 2.73/1.00  res_orphan_elimination:                 0
% 2.73/1.00  res_tautology_del:                      43
% 2.73/1.00  res_num_eq_res_simplified:              0
% 2.73/1.00  res_num_sel_changes:                    0
% 2.73/1.00  res_moves_from_active_to_pass:          0
% 2.73/1.00  
% 2.73/1.00  ------ Superposition
% 2.73/1.00  
% 2.73/1.00  sup_time_total:                         0.
% 2.73/1.00  sup_time_generating:                    0.
% 2.73/1.00  sup_time_sim_full:                      0.
% 2.73/1.00  sup_time_sim_immed:                     0.
% 2.73/1.00  
% 2.73/1.00  sup_num_of_clauses:                     68
% 2.73/1.00  sup_num_in_active:                      60
% 2.73/1.00  sup_num_in_passive:                     8
% 2.73/1.00  sup_num_of_loops:                       64
% 2.73/1.00  sup_fw_superposition:                   41
% 2.73/1.00  sup_bw_superposition:                   11
% 2.73/1.00  sup_immediate_simplified:               16
% 2.73/1.00  sup_given_eliminated:                   0
% 2.73/1.00  comparisons_done:                       0
% 2.73/1.00  comparisons_avoided:                    0
% 2.73/1.00  
% 2.73/1.00  ------ Simplifications
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  sim_fw_subset_subsumed:                 1
% 2.73/1.00  sim_bw_subset_subsumed:                 0
% 2.73/1.00  sim_fw_subsumed:                        3
% 2.73/1.00  sim_bw_subsumed:                        0
% 2.73/1.00  sim_fw_subsumption_res:                 0
% 2.73/1.00  sim_bw_subsumption_res:                 0
% 2.73/1.00  sim_tautology_del:                      0
% 2.73/1.00  sim_eq_tautology_del:                   4
% 2.73/1.00  sim_eq_res_simp:                        1
% 2.73/1.00  sim_fw_demodulated:                     7
% 2.73/1.00  sim_bw_demodulated:                     5
% 2.73/1.00  sim_light_normalised:                   12
% 2.73/1.00  sim_joinable_taut:                      0
% 2.73/1.00  sim_joinable_simp:                      0
% 2.73/1.00  sim_ac_normalised:                      0
% 2.73/1.00  sim_smt_subsumption:                    0
% 2.73/1.00  
%------------------------------------------------------------------------------
