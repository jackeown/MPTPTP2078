%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:50 EST 2020

% Result     : Theorem 23.81s
% Output     : CNFRefutation 23.81s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 701 expanded)
%              Number of clauses        :   78 ( 313 expanded)
%              Number of leaves         :   16 ( 129 expanded)
%              Depth                    :   19
%              Number of atoms          :  292 (1484 expanded)
%              Number of equality atoms :  121 ( 408 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f41])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f37])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f35])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_623,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_612,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_625,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1037,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_612,c_625])).

cnf(c_1420,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_1037])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_624,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_622,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_620,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1116,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k8_relat_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_620])).

cnf(c_70218,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_1116])).

cnf(c_70693,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_1420,c_70218])).

cnf(c_72126,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top
    | v1_relat_1(k8_relat_1(X0,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_70693,c_622])).

cnf(c_4638,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4639,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4638])).

cnf(c_72930,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72126,c_1420,c_4639])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_618,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_72942,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,X1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_72930,c_618])).

cnf(c_79088,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,sK3)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3) ),
    inference(superposition,[status(thm)],[c_1420,c_72942])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_3])).

cnf(c_611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_1034,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_612,c_611])).

cnf(c_1303,plain,
    ( k8_relat_1(sK0,sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_620])).

cnf(c_1473,plain,
    ( k8_relat_1(sK0,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1303,c_1420])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_617,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1715,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_617])).

cnf(c_3449,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1715,c_1420])).

cnf(c_3450,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3449])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1594,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_612,c_614])).

cnf(c_1881,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_625])).

cnf(c_1437,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1438,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1437])).

cnf(c_1974,plain,
    ( v1_relat_1(X0) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1881,c_1438])).

cnf(c_1975,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1974])).

cnf(c_3461,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3450,c_1975])).

cnf(c_1645,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1665,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_3538,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3461,c_1420,c_1665])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_619,plain,
    ( k8_relat_1(k2_relat_1(X0),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3548,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_3538,c_619])).

cnf(c_79120,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3) = k8_relat_1(X0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_79088,c_3548])).

cnf(c_79463,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_79120,c_3450])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4685,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4686,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4685])).

cnf(c_1423,plain,
    ( k8_relat_1(k2_relat_1(sK3),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1420,c_619])).

cnf(c_1716,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_617])).

cnf(c_6804,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1716,c_1420])).

cnf(c_6805,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6804])).

cnf(c_79455,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_79120,c_6805])).

cnf(c_79987,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_79463,c_1420,c_4686,c_79455])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_615,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1882,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_615])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_616,plain,
    ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1113,plain,
    ( k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_612,c_616])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_613,plain,
    ( m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1218,plain,
    ( m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1113,c_613])).

cnf(c_2564,plain,
    ( r1_tarski(k8_relat_1(sK1,sK3),sK3) != iProver_top
    | r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_1218])).

cnf(c_820,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK1,X0)),sK1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1646,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1663,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_2586,plain,
    ( r1_tarski(k8_relat_1(sK1,sK3),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2564,c_1420,c_1663])).

cnf(c_80014,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_79987,c_2586])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:43:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.81/3.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.81/3.48  
% 23.81/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.81/3.48  
% 23.81/3.48  ------  iProver source info
% 23.81/3.48  
% 23.81/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.81/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.81/3.48  git: non_committed_changes: false
% 23.81/3.48  git: last_make_outside_of_git: false
% 23.81/3.48  
% 23.81/3.48  ------ 
% 23.81/3.48  
% 23.81/3.48  ------ Input Options
% 23.81/3.48  
% 23.81/3.48  --out_options                           all
% 23.81/3.48  --tptp_safe_out                         true
% 23.81/3.48  --problem_path                          ""
% 23.81/3.48  --include_path                          ""
% 23.81/3.48  --clausifier                            res/vclausify_rel
% 23.81/3.48  --clausifier_options                    ""
% 23.81/3.48  --stdin                                 false
% 23.81/3.48  --stats_out                             all
% 23.81/3.48  
% 23.81/3.48  ------ General Options
% 23.81/3.48  
% 23.81/3.48  --fof                                   false
% 23.81/3.48  --time_out_real                         305.
% 23.81/3.48  --time_out_virtual                      -1.
% 23.81/3.48  --symbol_type_check                     false
% 23.81/3.48  --clausify_out                          false
% 23.81/3.48  --sig_cnt_out                           false
% 23.81/3.48  --trig_cnt_out                          false
% 23.81/3.48  --trig_cnt_out_tolerance                1.
% 23.81/3.48  --trig_cnt_out_sk_spl                   false
% 23.81/3.48  --abstr_cl_out                          false
% 23.81/3.48  
% 23.81/3.48  ------ Global Options
% 23.81/3.48  
% 23.81/3.48  --schedule                              default
% 23.81/3.48  --add_important_lit                     false
% 23.81/3.48  --prop_solver_per_cl                    1000
% 23.81/3.48  --min_unsat_core                        false
% 23.81/3.48  --soft_assumptions                      false
% 23.81/3.48  --soft_lemma_size                       3
% 23.81/3.48  --prop_impl_unit_size                   0
% 23.81/3.48  --prop_impl_unit                        []
% 23.81/3.48  --share_sel_clauses                     true
% 23.81/3.48  --reset_solvers                         false
% 23.81/3.48  --bc_imp_inh                            [conj_cone]
% 23.81/3.48  --conj_cone_tolerance                   3.
% 23.81/3.48  --extra_neg_conj                        none
% 23.81/3.48  --large_theory_mode                     true
% 23.81/3.48  --prolific_symb_bound                   200
% 23.81/3.48  --lt_threshold                          2000
% 23.81/3.48  --clause_weak_htbl                      true
% 23.81/3.48  --gc_record_bc_elim                     false
% 23.81/3.48  
% 23.81/3.48  ------ Preprocessing Options
% 23.81/3.48  
% 23.81/3.48  --preprocessing_flag                    true
% 23.81/3.48  --time_out_prep_mult                    0.1
% 23.81/3.48  --splitting_mode                        input
% 23.81/3.48  --splitting_grd                         true
% 23.81/3.48  --splitting_cvd                         false
% 23.81/3.48  --splitting_cvd_svl                     false
% 23.81/3.48  --splitting_nvd                         32
% 23.81/3.48  --sub_typing                            true
% 23.81/3.48  --prep_gs_sim                           true
% 23.81/3.48  --prep_unflatten                        true
% 23.81/3.48  --prep_res_sim                          true
% 23.81/3.48  --prep_upred                            true
% 23.81/3.48  --prep_sem_filter                       exhaustive
% 23.81/3.48  --prep_sem_filter_out                   false
% 23.81/3.48  --pred_elim                             true
% 23.81/3.48  --res_sim_input                         true
% 23.81/3.48  --eq_ax_congr_red                       true
% 23.81/3.48  --pure_diseq_elim                       true
% 23.81/3.48  --brand_transform                       false
% 23.81/3.48  --non_eq_to_eq                          false
% 23.81/3.48  --prep_def_merge                        true
% 23.81/3.48  --prep_def_merge_prop_impl              false
% 23.81/3.48  --prep_def_merge_mbd                    true
% 23.81/3.48  --prep_def_merge_tr_red                 false
% 23.81/3.48  --prep_def_merge_tr_cl                  false
% 23.81/3.48  --smt_preprocessing                     true
% 23.81/3.48  --smt_ac_axioms                         fast
% 23.81/3.48  --preprocessed_out                      false
% 23.81/3.48  --preprocessed_stats                    false
% 23.81/3.48  
% 23.81/3.48  ------ Abstraction refinement Options
% 23.81/3.48  
% 23.81/3.48  --abstr_ref                             []
% 23.81/3.48  --abstr_ref_prep                        false
% 23.81/3.48  --abstr_ref_until_sat                   false
% 23.81/3.48  --abstr_ref_sig_restrict                funpre
% 23.81/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.81/3.48  --abstr_ref_under                       []
% 23.81/3.48  
% 23.81/3.48  ------ SAT Options
% 23.81/3.48  
% 23.81/3.48  --sat_mode                              false
% 23.81/3.48  --sat_fm_restart_options                ""
% 23.81/3.48  --sat_gr_def                            false
% 23.81/3.48  --sat_epr_types                         true
% 23.81/3.48  --sat_non_cyclic_types                  false
% 23.81/3.48  --sat_finite_models                     false
% 23.81/3.48  --sat_fm_lemmas                         false
% 23.81/3.48  --sat_fm_prep                           false
% 23.81/3.48  --sat_fm_uc_incr                        true
% 23.81/3.48  --sat_out_model                         small
% 23.81/3.48  --sat_out_clauses                       false
% 23.81/3.48  
% 23.81/3.48  ------ QBF Options
% 23.81/3.48  
% 23.81/3.48  --qbf_mode                              false
% 23.81/3.48  --qbf_elim_univ                         false
% 23.81/3.48  --qbf_dom_inst                          none
% 23.81/3.48  --qbf_dom_pre_inst                      false
% 23.81/3.48  --qbf_sk_in                             false
% 23.81/3.48  --qbf_pred_elim                         true
% 23.81/3.48  --qbf_split                             512
% 23.81/3.48  
% 23.81/3.48  ------ BMC1 Options
% 23.81/3.48  
% 23.81/3.48  --bmc1_incremental                      false
% 23.81/3.48  --bmc1_axioms                           reachable_all
% 23.81/3.48  --bmc1_min_bound                        0
% 23.81/3.48  --bmc1_max_bound                        -1
% 23.81/3.48  --bmc1_max_bound_default                -1
% 23.81/3.48  --bmc1_symbol_reachability              true
% 23.81/3.48  --bmc1_property_lemmas                  false
% 23.81/3.48  --bmc1_k_induction                      false
% 23.81/3.48  --bmc1_non_equiv_states                 false
% 23.81/3.48  --bmc1_deadlock                         false
% 23.81/3.48  --bmc1_ucm                              false
% 23.81/3.48  --bmc1_add_unsat_core                   none
% 23.81/3.48  --bmc1_unsat_core_children              false
% 23.81/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.81/3.48  --bmc1_out_stat                         full
% 23.81/3.48  --bmc1_ground_init                      false
% 23.81/3.48  --bmc1_pre_inst_next_state              false
% 23.81/3.48  --bmc1_pre_inst_state                   false
% 23.81/3.48  --bmc1_pre_inst_reach_state             false
% 23.81/3.48  --bmc1_out_unsat_core                   false
% 23.81/3.48  --bmc1_aig_witness_out                  false
% 23.81/3.48  --bmc1_verbose                          false
% 23.81/3.48  --bmc1_dump_clauses_tptp                false
% 23.81/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.81/3.48  --bmc1_dump_file                        -
% 23.81/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.81/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.81/3.48  --bmc1_ucm_extend_mode                  1
% 23.81/3.48  --bmc1_ucm_init_mode                    2
% 23.81/3.48  --bmc1_ucm_cone_mode                    none
% 23.81/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.81/3.48  --bmc1_ucm_relax_model                  4
% 23.81/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.81/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.81/3.48  --bmc1_ucm_layered_model                none
% 23.81/3.48  --bmc1_ucm_max_lemma_size               10
% 23.81/3.48  
% 23.81/3.48  ------ AIG Options
% 23.81/3.48  
% 23.81/3.48  --aig_mode                              false
% 23.81/3.48  
% 23.81/3.48  ------ Instantiation Options
% 23.81/3.48  
% 23.81/3.48  --instantiation_flag                    true
% 23.81/3.48  --inst_sos_flag                         true
% 23.81/3.48  --inst_sos_phase                        true
% 23.81/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.81/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.81/3.48  --inst_lit_sel_side                     num_symb
% 23.81/3.48  --inst_solver_per_active                1400
% 23.81/3.48  --inst_solver_calls_frac                1.
% 23.81/3.48  --inst_passive_queue_type               priority_queues
% 23.81/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.81/3.48  --inst_passive_queues_freq              [25;2]
% 23.81/3.48  --inst_dismatching                      true
% 23.81/3.48  --inst_eager_unprocessed_to_passive     true
% 23.81/3.48  --inst_prop_sim_given                   true
% 23.81/3.48  --inst_prop_sim_new                     false
% 23.81/3.48  --inst_subs_new                         false
% 23.81/3.48  --inst_eq_res_simp                      false
% 23.81/3.48  --inst_subs_given                       false
% 23.81/3.48  --inst_orphan_elimination               true
% 23.81/3.48  --inst_learning_loop_flag               true
% 23.81/3.48  --inst_learning_start                   3000
% 23.81/3.48  --inst_learning_factor                  2
% 23.81/3.48  --inst_start_prop_sim_after_learn       3
% 23.81/3.48  --inst_sel_renew                        solver
% 23.81/3.48  --inst_lit_activity_flag                true
% 23.81/3.48  --inst_restr_to_given                   false
% 23.81/3.48  --inst_activity_threshold               500
% 23.81/3.48  --inst_out_proof                        true
% 23.81/3.48  
% 23.81/3.48  ------ Resolution Options
% 23.81/3.48  
% 23.81/3.48  --resolution_flag                       true
% 23.81/3.48  --res_lit_sel                           adaptive
% 23.81/3.48  --res_lit_sel_side                      none
% 23.81/3.48  --res_ordering                          kbo
% 23.81/3.48  --res_to_prop_solver                    active
% 23.81/3.48  --res_prop_simpl_new                    false
% 23.81/3.48  --res_prop_simpl_given                  true
% 23.81/3.48  --res_passive_queue_type                priority_queues
% 23.81/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.81/3.48  --res_passive_queues_freq               [15;5]
% 23.81/3.48  --res_forward_subs                      full
% 23.81/3.48  --res_backward_subs                     full
% 23.81/3.48  --res_forward_subs_resolution           true
% 23.81/3.48  --res_backward_subs_resolution          true
% 23.81/3.48  --res_orphan_elimination                true
% 23.81/3.48  --res_time_limit                        2.
% 23.81/3.48  --res_out_proof                         true
% 23.81/3.48  
% 23.81/3.48  ------ Superposition Options
% 23.81/3.48  
% 23.81/3.48  --superposition_flag                    true
% 23.81/3.48  --sup_passive_queue_type                priority_queues
% 23.81/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.81/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.81/3.48  --demod_completeness_check              fast
% 23.81/3.48  --demod_use_ground                      true
% 23.81/3.48  --sup_to_prop_solver                    passive
% 23.81/3.48  --sup_prop_simpl_new                    true
% 23.81/3.48  --sup_prop_simpl_given                  true
% 23.81/3.48  --sup_fun_splitting                     true
% 23.81/3.48  --sup_smt_interval                      50000
% 23.81/3.48  
% 23.81/3.48  ------ Superposition Simplification Setup
% 23.81/3.48  
% 23.81/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.81/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.81/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.81/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.81/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.81/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.81/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.81/3.48  --sup_immed_triv                        [TrivRules]
% 23.81/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.81/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.81/3.48  --sup_immed_bw_main                     []
% 23.81/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.81/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.81/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.81/3.48  --sup_input_bw                          []
% 23.81/3.48  
% 23.81/3.48  ------ Combination Options
% 23.81/3.48  
% 23.81/3.48  --comb_res_mult                         3
% 23.81/3.48  --comb_sup_mult                         2
% 23.81/3.48  --comb_inst_mult                        10
% 23.81/3.48  
% 23.81/3.48  ------ Debug Options
% 23.81/3.48  
% 23.81/3.48  --dbg_backtrace                         false
% 23.81/3.48  --dbg_dump_prop_clauses                 false
% 23.81/3.48  --dbg_dump_prop_clauses_file            -
% 23.81/3.48  --dbg_out_stat                          false
% 23.81/3.48  ------ Parsing...
% 23.81/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.81/3.48  
% 23.81/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.81/3.48  
% 23.81/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.81/3.48  
% 23.81/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.81/3.48  ------ Proving...
% 23.81/3.48  ------ Problem Properties 
% 23.81/3.48  
% 23.81/3.48  
% 23.81/3.48  clauses                                 16
% 23.81/3.48  conjectures                             2
% 23.81/3.48  EPR                                     1
% 23.81/3.48  Horn                                    16
% 23.81/3.48  unary                                   3
% 23.81/3.48  binary                                  5
% 23.81/3.48  lits                                    37
% 23.81/3.48  lits eq                                 4
% 23.81/3.48  fd_pure                                 0
% 23.81/3.48  fd_pseudo                               0
% 23.81/3.48  fd_cond                                 0
% 23.81/3.48  fd_pseudo_cond                          0
% 23.81/3.48  AC symbols                              0
% 23.81/3.48  
% 23.81/3.48  ------ Schedule dynamic 5 is on 
% 23.81/3.48  
% 23.81/3.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.81/3.48  
% 23.81/3.48  
% 23.81/3.48  ------ 
% 23.81/3.48  Current options:
% 23.81/3.48  ------ 
% 23.81/3.48  
% 23.81/3.48  ------ Input Options
% 23.81/3.48  
% 23.81/3.48  --out_options                           all
% 23.81/3.48  --tptp_safe_out                         true
% 23.81/3.48  --problem_path                          ""
% 23.81/3.48  --include_path                          ""
% 23.81/3.48  --clausifier                            res/vclausify_rel
% 23.81/3.48  --clausifier_options                    ""
% 23.81/3.48  --stdin                                 false
% 23.81/3.48  --stats_out                             all
% 23.81/3.48  
% 23.81/3.48  ------ General Options
% 23.81/3.48  
% 23.81/3.48  --fof                                   false
% 23.81/3.48  --time_out_real                         305.
% 23.81/3.48  --time_out_virtual                      -1.
% 23.81/3.48  --symbol_type_check                     false
% 23.81/3.48  --clausify_out                          false
% 23.81/3.48  --sig_cnt_out                           false
% 23.81/3.48  --trig_cnt_out                          false
% 23.81/3.48  --trig_cnt_out_tolerance                1.
% 23.81/3.48  --trig_cnt_out_sk_spl                   false
% 23.81/3.48  --abstr_cl_out                          false
% 23.81/3.48  
% 23.81/3.48  ------ Global Options
% 23.81/3.48  
% 23.81/3.48  --schedule                              default
% 23.81/3.48  --add_important_lit                     false
% 23.81/3.48  --prop_solver_per_cl                    1000
% 23.81/3.48  --min_unsat_core                        false
% 23.81/3.48  --soft_assumptions                      false
% 23.81/3.48  --soft_lemma_size                       3
% 23.81/3.48  --prop_impl_unit_size                   0
% 23.81/3.48  --prop_impl_unit                        []
% 23.81/3.48  --share_sel_clauses                     true
% 23.81/3.48  --reset_solvers                         false
% 23.81/3.48  --bc_imp_inh                            [conj_cone]
% 23.81/3.48  --conj_cone_tolerance                   3.
% 23.81/3.48  --extra_neg_conj                        none
% 23.81/3.48  --large_theory_mode                     true
% 23.81/3.48  --prolific_symb_bound                   200
% 23.81/3.48  --lt_threshold                          2000
% 23.81/3.48  --clause_weak_htbl                      true
% 23.81/3.48  --gc_record_bc_elim                     false
% 23.81/3.48  
% 23.81/3.48  ------ Preprocessing Options
% 23.81/3.48  
% 23.81/3.48  --preprocessing_flag                    true
% 23.81/3.48  --time_out_prep_mult                    0.1
% 23.81/3.48  --splitting_mode                        input
% 23.81/3.48  --splitting_grd                         true
% 23.81/3.48  --splitting_cvd                         false
% 23.81/3.48  --splitting_cvd_svl                     false
% 23.81/3.48  --splitting_nvd                         32
% 23.81/3.48  --sub_typing                            true
% 23.81/3.48  --prep_gs_sim                           true
% 23.81/3.48  --prep_unflatten                        true
% 23.81/3.48  --prep_res_sim                          true
% 23.81/3.48  --prep_upred                            true
% 23.81/3.48  --prep_sem_filter                       exhaustive
% 23.81/3.48  --prep_sem_filter_out                   false
% 23.81/3.48  --pred_elim                             true
% 23.81/3.48  --res_sim_input                         true
% 23.81/3.48  --eq_ax_congr_red                       true
% 23.81/3.48  --pure_diseq_elim                       true
% 23.81/3.48  --brand_transform                       false
% 23.81/3.48  --non_eq_to_eq                          false
% 23.81/3.48  --prep_def_merge                        true
% 23.81/3.48  --prep_def_merge_prop_impl              false
% 23.81/3.48  --prep_def_merge_mbd                    true
% 23.81/3.48  --prep_def_merge_tr_red                 false
% 23.81/3.48  --prep_def_merge_tr_cl                  false
% 23.81/3.48  --smt_preprocessing                     true
% 23.81/3.48  --smt_ac_axioms                         fast
% 23.81/3.48  --preprocessed_out                      false
% 23.81/3.48  --preprocessed_stats                    false
% 23.81/3.48  
% 23.81/3.48  ------ Abstraction refinement Options
% 23.81/3.48  
% 23.81/3.48  --abstr_ref                             []
% 23.81/3.48  --abstr_ref_prep                        false
% 23.81/3.48  --abstr_ref_until_sat                   false
% 23.81/3.48  --abstr_ref_sig_restrict                funpre
% 23.81/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.81/3.48  --abstr_ref_under                       []
% 23.81/3.48  
% 23.81/3.48  ------ SAT Options
% 23.81/3.48  
% 23.81/3.48  --sat_mode                              false
% 23.81/3.48  --sat_fm_restart_options                ""
% 23.81/3.48  --sat_gr_def                            false
% 23.81/3.48  --sat_epr_types                         true
% 23.81/3.48  --sat_non_cyclic_types                  false
% 23.81/3.48  --sat_finite_models                     false
% 23.81/3.48  --sat_fm_lemmas                         false
% 23.81/3.48  --sat_fm_prep                           false
% 23.81/3.48  --sat_fm_uc_incr                        true
% 23.81/3.48  --sat_out_model                         small
% 23.81/3.48  --sat_out_clauses                       false
% 23.81/3.48  
% 23.81/3.48  ------ QBF Options
% 23.81/3.48  
% 23.81/3.48  --qbf_mode                              false
% 23.81/3.48  --qbf_elim_univ                         false
% 23.81/3.48  --qbf_dom_inst                          none
% 23.81/3.48  --qbf_dom_pre_inst                      false
% 23.81/3.48  --qbf_sk_in                             false
% 23.81/3.48  --qbf_pred_elim                         true
% 23.81/3.48  --qbf_split                             512
% 23.81/3.48  
% 23.81/3.48  ------ BMC1 Options
% 23.81/3.48  
% 23.81/3.48  --bmc1_incremental                      false
% 23.81/3.48  --bmc1_axioms                           reachable_all
% 23.81/3.48  --bmc1_min_bound                        0
% 23.81/3.48  --bmc1_max_bound                        -1
% 23.81/3.48  --bmc1_max_bound_default                -1
% 23.81/3.48  --bmc1_symbol_reachability              true
% 23.81/3.48  --bmc1_property_lemmas                  false
% 23.81/3.48  --bmc1_k_induction                      false
% 23.81/3.48  --bmc1_non_equiv_states                 false
% 23.81/3.48  --bmc1_deadlock                         false
% 23.81/3.48  --bmc1_ucm                              false
% 23.81/3.48  --bmc1_add_unsat_core                   none
% 23.81/3.48  --bmc1_unsat_core_children              false
% 23.81/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.81/3.48  --bmc1_out_stat                         full
% 23.81/3.48  --bmc1_ground_init                      false
% 23.81/3.48  --bmc1_pre_inst_next_state              false
% 23.81/3.48  --bmc1_pre_inst_state                   false
% 23.81/3.48  --bmc1_pre_inst_reach_state             false
% 23.81/3.48  --bmc1_out_unsat_core                   false
% 23.81/3.48  --bmc1_aig_witness_out                  false
% 23.81/3.48  --bmc1_verbose                          false
% 23.81/3.48  --bmc1_dump_clauses_tptp                false
% 23.81/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.81/3.48  --bmc1_dump_file                        -
% 23.81/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.81/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.81/3.48  --bmc1_ucm_extend_mode                  1
% 23.81/3.48  --bmc1_ucm_init_mode                    2
% 23.81/3.48  --bmc1_ucm_cone_mode                    none
% 23.81/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.81/3.48  --bmc1_ucm_relax_model                  4
% 23.81/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.81/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.81/3.48  --bmc1_ucm_layered_model                none
% 23.81/3.48  --bmc1_ucm_max_lemma_size               10
% 23.81/3.48  
% 23.81/3.48  ------ AIG Options
% 23.81/3.48  
% 23.81/3.48  --aig_mode                              false
% 23.81/3.48  
% 23.81/3.48  ------ Instantiation Options
% 23.81/3.48  
% 23.81/3.48  --instantiation_flag                    true
% 23.81/3.48  --inst_sos_flag                         true
% 23.81/3.48  --inst_sos_phase                        true
% 23.81/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.81/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.81/3.48  --inst_lit_sel_side                     none
% 23.81/3.48  --inst_solver_per_active                1400
% 23.81/3.48  --inst_solver_calls_frac                1.
% 23.81/3.48  --inst_passive_queue_type               priority_queues
% 23.81/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.81/3.48  --inst_passive_queues_freq              [25;2]
% 23.81/3.48  --inst_dismatching                      true
% 23.81/3.48  --inst_eager_unprocessed_to_passive     true
% 23.81/3.48  --inst_prop_sim_given                   true
% 23.81/3.48  --inst_prop_sim_new                     false
% 23.81/3.48  --inst_subs_new                         false
% 23.81/3.48  --inst_eq_res_simp                      false
% 23.81/3.48  --inst_subs_given                       false
% 23.81/3.48  --inst_orphan_elimination               true
% 23.81/3.48  --inst_learning_loop_flag               true
% 23.81/3.48  --inst_learning_start                   3000
% 23.81/3.48  --inst_learning_factor                  2
% 23.81/3.48  --inst_start_prop_sim_after_learn       3
% 23.81/3.48  --inst_sel_renew                        solver
% 23.81/3.48  --inst_lit_activity_flag                true
% 23.81/3.48  --inst_restr_to_given                   false
% 23.81/3.48  --inst_activity_threshold               500
% 23.81/3.48  --inst_out_proof                        true
% 23.81/3.48  
% 23.81/3.48  ------ Resolution Options
% 23.81/3.48  
% 23.81/3.48  --resolution_flag                       false
% 23.81/3.48  --res_lit_sel                           adaptive
% 23.81/3.48  --res_lit_sel_side                      none
% 23.81/3.48  --res_ordering                          kbo
% 23.81/3.48  --res_to_prop_solver                    active
% 23.81/3.48  --res_prop_simpl_new                    false
% 23.81/3.48  --res_prop_simpl_given                  true
% 23.81/3.48  --res_passive_queue_type                priority_queues
% 23.81/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.81/3.48  --res_passive_queues_freq               [15;5]
% 23.81/3.48  --res_forward_subs                      full
% 23.81/3.48  --res_backward_subs                     full
% 23.81/3.48  --res_forward_subs_resolution           true
% 23.81/3.48  --res_backward_subs_resolution          true
% 23.81/3.48  --res_orphan_elimination                true
% 23.81/3.48  --res_time_limit                        2.
% 23.81/3.48  --res_out_proof                         true
% 23.81/3.48  
% 23.81/3.48  ------ Superposition Options
% 23.81/3.48  
% 23.81/3.48  --superposition_flag                    true
% 23.81/3.48  --sup_passive_queue_type                priority_queues
% 23.81/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.81/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.81/3.48  --demod_completeness_check              fast
% 23.81/3.48  --demod_use_ground                      true
% 23.81/3.48  --sup_to_prop_solver                    passive
% 23.81/3.48  --sup_prop_simpl_new                    true
% 23.81/3.48  --sup_prop_simpl_given                  true
% 23.81/3.48  --sup_fun_splitting                     true
% 23.81/3.48  --sup_smt_interval                      50000
% 23.81/3.48  
% 23.81/3.48  ------ Superposition Simplification Setup
% 23.81/3.48  
% 23.81/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.81/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.81/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.81/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.81/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.81/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.81/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.81/3.48  --sup_immed_triv                        [TrivRules]
% 23.81/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.81/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.81/3.48  --sup_immed_bw_main                     []
% 23.81/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.81/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.81/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.81/3.48  --sup_input_bw                          []
% 23.81/3.48  
% 23.81/3.48  ------ Combination Options
% 23.81/3.48  
% 23.81/3.48  --comb_res_mult                         3
% 23.81/3.48  --comb_sup_mult                         2
% 23.81/3.48  --comb_inst_mult                        10
% 23.81/3.48  
% 23.81/3.48  ------ Debug Options
% 23.81/3.48  
% 23.81/3.48  --dbg_backtrace                         false
% 23.81/3.48  --dbg_dump_prop_clauses                 false
% 23.81/3.48  --dbg_dump_prop_clauses_file            -
% 23.81/3.48  --dbg_out_stat                          false
% 23.81/3.48  
% 23.81/3.48  
% 23.81/3.48  
% 23.81/3.48  
% 23.81/3.48  ------ Proving...
% 23.81/3.48  
% 23.81/3.48  
% 23.81/3.48  % SZS status Theorem for theBenchmark.p
% 23.81/3.48  
% 23.81/3.48   Resolution empty clause
% 23.81/3.48  
% 23.81/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.81/3.48  
% 23.81/3.48  fof(f5,axiom,(
% 23.81/3.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f48,plain,(
% 23.81/3.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 23.81/3.48    inference(cnf_transformation,[],[f5])).
% 23.81/3.48  
% 23.81/3.48  fof(f16,conjecture,(
% 23.81/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f17,negated_conjecture,(
% 23.81/3.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 23.81/3.48    inference(negated_conjecture,[],[f16])).
% 23.81/3.48  
% 23.81/3.48  fof(f39,plain,(
% 23.81/3.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 23.81/3.48    inference(ennf_transformation,[],[f17])).
% 23.81/3.48  
% 23.81/3.48  fof(f41,plain,(
% 23.81/3.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 23.81/3.48    introduced(choice_axiom,[])).
% 23.81/3.48  
% 23.81/3.48  fof(f42,plain,(
% 23.81/3.48    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 23.81/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f41])).
% 23.81/3.48  
% 23.81/3.48  fof(f59,plain,(
% 23.81/3.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 23.81/3.48    inference(cnf_transformation,[],[f42])).
% 23.81/3.48  
% 23.81/3.48  fof(f2,axiom,(
% 23.81/3.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f21,plain,(
% 23.81/3.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 23.81/3.48    inference(ennf_transformation,[],[f2])).
% 23.81/3.48  
% 23.81/3.48  fof(f44,plain,(
% 23.81/3.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f21])).
% 23.81/3.48  
% 23.81/3.48  fof(f4,axiom,(
% 23.81/3.48    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f23,plain,(
% 23.81/3.48    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 23.81/3.48    inference(ennf_transformation,[],[f4])).
% 23.81/3.48  
% 23.81/3.48  fof(f47,plain,(
% 23.81/3.48    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f23])).
% 23.81/3.48  
% 23.81/3.48  fof(f6,axiom,(
% 23.81/3.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f24,plain,(
% 23.81/3.48    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 23.81/3.48    inference(ennf_transformation,[],[f6])).
% 23.81/3.48  
% 23.81/3.48  fof(f49,plain,(
% 23.81/3.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f24])).
% 23.81/3.48  
% 23.81/3.48  fof(f8,axiom,(
% 23.81/3.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f26,plain,(
% 23.81/3.48    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.81/3.48    inference(ennf_transformation,[],[f8])).
% 23.81/3.48  
% 23.81/3.48  fof(f27,plain,(
% 23.81/3.48    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 23.81/3.48    inference(flattening,[],[f26])).
% 23.81/3.48  
% 23.81/3.48  fof(f51,plain,(
% 23.81/3.48    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f27])).
% 23.81/3.48  
% 23.81/3.48  fof(f10,axiom,(
% 23.81/3.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f29,plain,(
% 23.81/3.48    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 23.81/3.48    inference(ennf_transformation,[],[f10])).
% 23.81/3.48  
% 23.81/3.48  fof(f30,plain,(
% 23.81/3.48    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 23.81/3.48    inference(flattening,[],[f29])).
% 23.81/3.48  
% 23.81/3.48  fof(f53,plain,(
% 23.81/3.48    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f30])).
% 23.81/3.48  
% 23.81/3.48  fof(f12,axiom,(
% 23.81/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f18,plain,(
% 23.81/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 23.81/3.48    inference(pure_predicate_removal,[],[f12])).
% 23.81/3.48  
% 23.81/3.48  fof(f33,plain,(
% 23.81/3.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.81/3.48    inference(ennf_transformation,[],[f18])).
% 23.81/3.48  
% 23.81/3.48  fof(f55,plain,(
% 23.81/3.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.81/3.48    inference(cnf_transformation,[],[f33])).
% 23.81/3.48  
% 23.81/3.48  fof(f3,axiom,(
% 23.81/3.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f22,plain,(
% 23.81/3.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.81/3.48    inference(ennf_transformation,[],[f3])).
% 23.81/3.48  
% 23.81/3.48  fof(f40,plain,(
% 23.81/3.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.81/3.48    inference(nnf_transformation,[],[f22])).
% 23.81/3.48  
% 23.81/3.48  fof(f45,plain,(
% 23.81/3.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f40])).
% 23.81/3.48  
% 23.81/3.48  fof(f11,axiom,(
% 23.81/3.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f31,plain,(
% 23.81/3.48    ! [X0,X1,X2] : ((r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 23.81/3.48    inference(ennf_transformation,[],[f11])).
% 23.81/3.48  
% 23.81/3.48  fof(f32,plain,(
% 23.81/3.48    ! [X0,X1,X2] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 23.81/3.48    inference(flattening,[],[f31])).
% 23.81/3.48  
% 23.81/3.48  fof(f54,plain,(
% 23.81/3.48    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f32])).
% 23.81/3.48  
% 23.81/3.48  fof(f15,axiom,(
% 23.81/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f37,plain,(
% 23.81/3.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.81/3.48    inference(ennf_transformation,[],[f15])).
% 23.81/3.48  
% 23.81/3.48  fof(f38,plain,(
% 23.81/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.81/3.48    inference(flattening,[],[f37])).
% 23.81/3.48  
% 23.81/3.48  fof(f58,plain,(
% 23.81/3.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 23.81/3.48    inference(cnf_transformation,[],[f38])).
% 23.81/3.48  
% 23.81/3.48  fof(f9,axiom,(
% 23.81/3.48    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f28,plain,(
% 23.81/3.48    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 23.81/3.48    inference(ennf_transformation,[],[f9])).
% 23.81/3.48  
% 23.81/3.48  fof(f52,plain,(
% 23.81/3.48    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f28])).
% 23.81/3.48  
% 23.81/3.48  fof(f7,axiom,(
% 23.81/3.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f25,plain,(
% 23.81/3.48    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.81/3.48    inference(ennf_transformation,[],[f7])).
% 23.81/3.48  
% 23.81/3.48  fof(f50,plain,(
% 23.81/3.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.81/3.48    inference(cnf_transformation,[],[f25])).
% 23.81/3.48  
% 23.81/3.48  fof(f14,axiom,(
% 23.81/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f35,plain,(
% 23.81/3.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 23.81/3.48    inference(ennf_transformation,[],[f14])).
% 23.81/3.48  
% 23.81/3.48  fof(f36,plain,(
% 23.81/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 23.81/3.48    inference(flattening,[],[f35])).
% 23.81/3.48  
% 23.81/3.48  fof(f57,plain,(
% 23.81/3.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 23.81/3.48    inference(cnf_transformation,[],[f36])).
% 23.81/3.48  
% 23.81/3.48  fof(f13,axiom,(
% 23.81/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 23.81/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.81/3.48  
% 23.81/3.48  fof(f34,plain,(
% 23.81/3.48    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.81/3.48    inference(ennf_transformation,[],[f13])).
% 23.81/3.48  
% 23.81/3.48  fof(f56,plain,(
% 23.81/3.48    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.81/3.48    inference(cnf_transformation,[],[f34])).
% 23.81/3.48  
% 23.81/3.48  fof(f60,plain,(
% 23.81/3.48    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 23.81/3.48    inference(cnf_transformation,[],[f42])).
% 23.81/3.48  
% 23.81/3.48  cnf(c_5,plain,
% 23.81/3.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 23.81/3.48      inference(cnf_transformation,[],[f48]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_623,plain,
% 23.81/3.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_17,negated_conjecture,
% 23.81/3.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 23.81/3.48      inference(cnf_transformation,[],[f59]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_612,plain,
% 23.81/3.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1,plain,
% 23.81/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 23.81/3.48      inference(cnf_transformation,[],[f44]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_625,plain,
% 23.81/3.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.81/3.48      | v1_relat_1(X1) != iProver_top
% 23.81/3.48      | v1_relat_1(X0) = iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1037,plain,
% 23.81/3.48      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 23.81/3.48      | v1_relat_1(sK3) = iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_612,c_625]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1420,plain,
% 23.81/3.48      ( v1_relat_1(sK3) = iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_623,c_1037]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_4,plain,
% 23.81/3.48      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 23.81/3.48      inference(cnf_transformation,[],[f47]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_624,plain,
% 23.81/3.48      ( v1_relat_1(X0) != iProver_top
% 23.81/3.48      | v1_relat_1(k8_relat_1(X1,X0)) = iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_6,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~ v1_relat_1(X1) ),
% 23.81/3.48      inference(cnf_transformation,[],[f49]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_622,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) = iProver_top
% 23.81/3.48      | v1_relat_1(X1) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_8,plain,
% 23.81/3.48      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 23.81/3.48      | ~ v1_relat_1(X0)
% 23.81/3.48      | k8_relat_1(X1,X0) = X0 ),
% 23.81/3.48      inference(cnf_transformation,[],[f51]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_620,plain,
% 23.81/3.48      ( k8_relat_1(X0,X1) = X1
% 23.81/3.48      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 23.81/3.48      | v1_relat_1(X1) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1116,plain,
% 23.81/3.48      ( k8_relat_1(X0,k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
% 23.81/3.48      | v1_relat_1(X1) != iProver_top
% 23.81/3.48      | v1_relat_1(k8_relat_1(X0,X1)) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_622,c_620]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_70218,plain,
% 23.81/3.48      ( k8_relat_1(X0,k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
% 23.81/3.48      | v1_relat_1(X1) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_624,c_1116]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_70693,plain,
% 23.81/3.48      ( k8_relat_1(X0,k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK3) ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1420,c_70218]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_72126,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top
% 23.81/3.48      | v1_relat_1(k8_relat_1(X0,sK3)) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_70693,c_622]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_4638,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) | ~ v1_relat_1(sK3) ),
% 23.81/3.48      inference(instantiation,[status(thm)],[c_6]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_4639,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top
% 23.81/3.48      | v1_relat_1(sK3) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_4638]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_72930,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top ),
% 23.81/3.48      inference(global_propositional_subsumption,
% 23.81/3.48                [status(thm)],
% 23.81/3.48                [c_72126,c_1420,c_4639]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_10,plain,
% 23.81/3.48      ( ~ r1_tarski(X0,X1)
% 23.81/3.48      | ~ v1_relat_1(X2)
% 23.81/3.48      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ),
% 23.81/3.48      inference(cnf_transformation,[],[f53]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_618,plain,
% 23.81/3.48      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
% 23.81/3.48      | r1_tarski(X0,X1) != iProver_top
% 23.81/3.48      | v1_relat_1(X2) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_72942,plain,
% 23.81/3.48      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,X1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),X1)
% 23.81/3.48      | v1_relat_1(X1) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_72930,c_618]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_79088,plain,
% 23.81/3.48      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,sK3)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3) ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1420,c_72942]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_12,plain,
% 23.81/3.48      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 23.81/3.48      inference(cnf_transformation,[],[f55]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_3,plain,
% 23.81/3.48      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 23.81/3.48      inference(cnf_transformation,[],[f45]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_203,plain,
% 23.81/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.81/3.48      | r1_tarski(k2_relat_1(X0),X2)
% 23.81/3.48      | ~ v1_relat_1(X0) ),
% 23.81/3.48      inference(resolution,[status(thm)],[c_12,c_3]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_611,plain,
% 23.81/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.81/3.48      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 23.81/3.48      | v1_relat_1(X0) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1034,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 23.81/3.48      | v1_relat_1(sK3) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_612,c_611]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1303,plain,
% 23.81/3.48      ( k8_relat_1(sK0,sK3) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1034,c_620]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1473,plain,
% 23.81/3.48      ( k8_relat_1(sK0,sK3) = sK3 ),
% 23.81/3.48      inference(global_propositional_subsumption,[status(thm)],[c_1303,c_1420]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_11,plain,
% 23.81/3.48      ( ~ r1_tarski(X0,X1)
% 23.81/3.48      | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
% 23.81/3.48      | ~ v1_relat_1(X2) ),
% 23.81/3.48      inference(cnf_transformation,[],[f54]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_617,plain,
% 23.81/3.48      ( r1_tarski(X0,X1) != iProver_top
% 23.81/3.48      | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = iProver_top
% 23.81/3.48      | v1_relat_1(X2) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1715,plain,
% 23.81/3.48      ( r1_tarski(X0,sK0) != iProver_top
% 23.81/3.48      | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 23.81/3.48      | v1_relat_1(sK3) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1473,c_617]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_3449,plain,
% 23.81/3.48      ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 23.81/3.48      | r1_tarski(X0,sK0) != iProver_top ),
% 23.81/3.48      inference(global_propositional_subsumption,[status(thm)],[c_1715,c_1420]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_3450,plain,
% 23.81/3.48      ( r1_tarski(X0,sK0) != iProver_top
% 23.81/3.48      | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
% 23.81/3.48      inference(renaming,[status(thm)],[c_3449]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_15,plain,
% 23.81/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.81/3.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.81/3.48      | ~ r1_tarski(X3,X0) ),
% 23.81/3.48      inference(cnf_transformation,[],[f58]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_614,plain,
% 23.81/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.81/3.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 23.81/3.48      | r1_tarski(X3,X0) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1594,plain,
% 23.81/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top
% 23.81/3.48      | r1_tarski(X0,sK3) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_612,c_614]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1881,plain,
% 23.81/3.48      ( r1_tarski(X0,sK3) != iProver_top
% 23.81/3.48      | v1_relat_1(X0) = iProver_top
% 23.81/3.48      | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1594,c_625]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1437,plain,
% 23.81/3.48      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
% 23.81/3.48      inference(instantiation,[status(thm)],[c_5]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1438,plain,
% 23.81/3.48      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_1437]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1974,plain,
% 23.81/3.48      ( v1_relat_1(X0) = iProver_top | r1_tarski(X0,sK3) != iProver_top ),
% 23.81/3.48      inference(global_propositional_subsumption,[status(thm)],[c_1881,c_1438]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1975,plain,
% 23.81/3.48      ( r1_tarski(X0,sK3) != iProver_top | v1_relat_1(X0) = iProver_top ),
% 23.81/3.48      inference(renaming,[status(thm)],[c_1974]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_3461,plain,
% 23.81/3.48      ( r1_tarski(X0,sK0) != iProver_top
% 23.81/3.48      | v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_3450,c_1975]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1645,plain,
% 23.81/3.48      ( v1_relat_1(k8_relat_1(X0,sK3)) | ~ v1_relat_1(sK3) ),
% 23.81/3.48      inference(instantiation,[status(thm)],[c_4]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1665,plain,
% 23.81/3.48      ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top
% 23.81/3.48      | v1_relat_1(sK3) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_3538,plain,
% 23.81/3.48      ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
% 23.81/3.48      inference(global_propositional_subsumption,
% 23.81/3.48                [status(thm)],
% 23.81/3.48                [c_3461,c_1420,c_1665]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_9,plain,
% 23.81/3.48      ( ~ v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
% 23.81/3.48      inference(cnf_transformation,[],[f52]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_619,plain,
% 23.81/3.48      ( k8_relat_1(k2_relat_1(X0),X0) = X0 | v1_relat_1(X0) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_3548,plain,
% 23.81/3.48      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK3) ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_3538,c_619]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_79120,plain,
% 23.81/3.48      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3) = k8_relat_1(X0,sK3) ),
% 23.81/3.48      inference(light_normalisation,[status(thm)],[c_79088,c_3548]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_79463,plain,
% 23.81/3.48      ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 23.81/3.48      | r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),sK0) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_79120,c_3450]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_7,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
% 23.81/3.48      | ~ v1_relat_1(X1) ),
% 23.81/3.48      inference(cnf_transformation,[],[f50]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_4685,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3))
% 23.81/3.48      | ~ v1_relat_1(sK3) ),
% 23.81/3.48      inference(instantiation,[status(thm)],[c_7]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_4686,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3)) = iProver_top
% 23.81/3.48      | v1_relat_1(sK3) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_4685]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1423,plain,
% 23.81/3.48      ( k8_relat_1(k2_relat_1(sK3),sK3) = sK3 ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1420,c_619]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1716,plain,
% 23.81/3.48      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 23.81/3.48      | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 23.81/3.48      | v1_relat_1(sK3) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1423,c_617]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_6804,plain,
% 23.81/3.48      ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 23.81/3.48      | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
% 23.81/3.48      inference(global_propositional_subsumption,[status(thm)],[c_1716,c_1420]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_6805,plain,
% 23.81/3.48      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 23.81/3.48      | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
% 23.81/3.48      inference(renaming,[status(thm)],[c_6804]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_79455,plain,
% 23.81/3.48      ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 23.81/3.48      | r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3)) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_79120,c_6805]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_79987,plain,
% 23.81/3.48      ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
% 23.81/3.48      inference(global_propositional_subsumption,
% 23.81/3.48                [status(thm)],
% 23.81/3.48                [c_79463,c_1420,c_4686,c_79455]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_14,plain,
% 23.81/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.81/3.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 23.81/3.48      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 23.81/3.48      inference(cnf_transformation,[],[f57]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_615,plain,
% 23.81/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.81/3.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 23.81/3.48      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1882,plain,
% 23.81/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) = iProver_top
% 23.81/3.48      | r1_tarski(X0,sK3) != iProver_top
% 23.81/3.48      | r1_tarski(k2_relat_1(X0),X1) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1594,c_615]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_13,plain,
% 23.81/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.81/3.48      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 23.81/3.48      inference(cnf_transformation,[],[f56]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_616,plain,
% 23.81/3.48      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
% 23.81/3.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1113,plain,
% 23.81/3.48      ( k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3) ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_612,c_616]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_16,negated_conjecture,
% 23.81/3.48      ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 23.81/3.48      inference(cnf_transformation,[],[f60]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_613,plain,
% 23.81/3.48      ( m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1218,plain,
% 23.81/3.48      ( m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 23.81/3.48      inference(demodulation,[status(thm)],[c_1113,c_613]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_2564,plain,
% 23.81/3.48      ( r1_tarski(k8_relat_1(sK1,sK3),sK3) != iProver_top
% 23.81/3.48      | r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_1882,c_1218]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_820,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(sK1,X0)),sK1) | ~ v1_relat_1(X0) ),
% 23.81/3.48      inference(instantiation,[status(thm)],[c_6]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1646,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) | ~ v1_relat_1(sK3) ),
% 23.81/3.48      inference(instantiation,[status(thm)],[c_820]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_1663,plain,
% 23.81/3.48      ( r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) = iProver_top
% 23.81/3.48      | v1_relat_1(sK3) != iProver_top ),
% 23.81/3.48      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_2586,plain,
% 23.81/3.48      ( r1_tarski(k8_relat_1(sK1,sK3),sK3) != iProver_top ),
% 23.81/3.48      inference(global_propositional_subsumption,
% 23.81/3.48                [status(thm)],
% 23.81/3.48                [c_2564,c_1420,c_1663]) ).
% 23.81/3.48  
% 23.81/3.48  cnf(c_80014,plain,
% 23.81/3.48      ( $false ),
% 23.81/3.48      inference(superposition,[status(thm)],[c_79987,c_2586]) ).
% 23.81/3.48  
% 23.81/3.48  
% 23.81/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.81/3.48  
% 23.81/3.48  ------                               Statistics
% 23.81/3.48  
% 23.81/3.48  ------ General
% 23.81/3.48  
% 23.81/3.48  abstr_ref_over_cycles:                  0
% 23.81/3.48  abstr_ref_under_cycles:                 0
% 23.81/3.48  gc_basic_clause_elim:                   0
% 23.81/3.48  forced_gc_time:                         0
% 23.81/3.48  parsing_time:                           0.007
% 23.81/3.48  unif_index_cands_time:                  0.
% 23.81/3.48  unif_index_add_time:                    0.
% 23.81/3.48  orderings_time:                         0.
% 23.81/3.48  out_proof_time:                         0.022
% 23.81/3.48  total_time:                             2.679
% 23.81/3.48  num_of_symbols:                         44
% 23.81/3.48  num_of_terms:                           138734
% 23.81/3.48  
% 23.81/3.48  ------ Preprocessing
% 23.81/3.48  
% 23.81/3.48  num_of_splits:                          0
% 23.81/3.48  num_of_split_atoms:                     0
% 23.81/3.48  num_of_reused_defs:                     0
% 23.81/3.48  num_eq_ax_congr_red:                    2
% 23.81/3.48  num_of_sem_filtered_clauses:            1
% 23.81/3.48  num_of_subtypes:                        0
% 23.81/3.48  monotx_restored_types:                  0
% 23.81/3.48  sat_num_of_epr_types:                   0
% 23.81/3.48  sat_num_of_non_cyclic_types:            0
% 23.81/3.48  sat_guarded_non_collapsed_types:        0
% 23.81/3.48  num_pure_diseq_elim:                    0
% 23.81/3.48  simp_replaced_by:                       0
% 23.81/3.48  res_preprocessed:                       87
% 23.81/3.48  prep_upred:                             0
% 23.81/3.48  prep_unflattend:                        0
% 23.81/3.48  smt_new_axioms:                         0
% 23.81/3.48  pred_elim_cands:                        3
% 23.81/3.48  pred_elim:                              1
% 23.81/3.48  pred_elim_cl:                           2
% 23.81/3.48  pred_elim_cycles:                       3
% 23.81/3.48  merged_defs:                            0
% 23.81/3.48  merged_defs_ncl:                        0
% 23.81/3.48  bin_hyper_res:                          0
% 23.81/3.48  prep_cycles:                            4
% 23.81/3.48  pred_elim_time:                         0.
% 23.81/3.48  splitting_time:                         0.
% 23.81/3.48  sem_filter_time:                        0.
% 23.81/3.48  monotx_time:                            0.
% 23.81/3.48  subtype_inf_time:                       0.
% 23.81/3.48  
% 23.81/3.48  ------ Problem properties
% 23.81/3.48  
% 23.81/3.48  clauses:                                16
% 23.81/3.48  conjectures:                            2
% 23.81/3.48  epr:                                    1
% 23.81/3.48  horn:                                   16
% 23.81/3.48  ground:                                 2
% 23.81/3.48  unary:                                  3
% 23.81/3.48  binary:                                 5
% 23.81/3.48  lits:                                   37
% 23.81/3.48  lits_eq:                                4
% 23.81/3.48  fd_pure:                                0
% 23.81/3.48  fd_pseudo:                              0
% 23.81/3.48  fd_cond:                                0
% 23.81/3.48  fd_pseudo_cond:                         0
% 23.81/3.48  ac_symbols:                             0
% 23.81/3.48  
% 23.81/3.48  ------ Propositional Solver
% 23.81/3.48  
% 23.81/3.48  prop_solver_calls:                      43
% 23.81/3.48  prop_fast_solver_calls:                 1520
% 23.81/3.48  smt_solver_calls:                       0
% 23.81/3.48  smt_fast_solver_calls:                  0
% 23.81/3.48  prop_num_of_clauses:                    42740
% 23.81/3.48  prop_preprocess_simplified:             55701
% 23.81/3.48  prop_fo_subsumed:                       82
% 23.81/3.48  prop_solver_time:                       0.
% 23.81/3.48  smt_solver_time:                        0.
% 23.81/3.48  smt_fast_solver_time:                   0.
% 23.81/3.48  prop_fast_solver_time:                  0.
% 23.81/3.48  prop_unsat_core_time:                   0.
% 23.81/3.48  
% 23.81/3.48  ------ QBF
% 23.81/3.48  
% 23.81/3.48  qbf_q_res:                              0
% 23.81/3.48  qbf_num_tautologies:                    0
% 23.81/3.48  qbf_prep_cycles:                        0
% 23.81/3.48  
% 23.81/3.48  ------ BMC1
% 23.81/3.48  
% 23.81/3.48  bmc1_current_bound:                     -1
% 23.81/3.48  bmc1_last_solved_bound:                 -1
% 23.81/3.48  bmc1_unsat_core_size:                   -1
% 23.81/3.48  bmc1_unsat_core_parents_size:           -1
% 23.81/3.48  bmc1_merge_next_fun:                    0
% 23.81/3.48  bmc1_unsat_core_clauses_time:           0.
% 23.81/3.48  
% 23.81/3.48  ------ Instantiation
% 23.81/3.48  
% 23.81/3.48  inst_num_of_clauses:                    7901
% 23.81/3.48  inst_num_in_passive:                    3631
% 23.81/3.48  inst_num_in_active:                     2239
% 23.81/3.48  inst_num_in_unprocessed:                2031
% 23.81/3.48  inst_num_of_loops:                      2350
% 23.81/3.48  inst_num_of_learning_restarts:          0
% 23.81/3.48  inst_num_moves_active_passive:          106
% 23.81/3.48  inst_lit_activity:                      0
% 23.81/3.48  inst_lit_activity_moves:                3
% 23.81/3.48  inst_num_tautologies:                   0
% 23.81/3.48  inst_num_prop_implied:                  0
% 23.81/3.48  inst_num_existing_simplified:           0
% 23.81/3.48  inst_num_eq_res_simplified:             0
% 23.81/3.48  inst_num_child_elim:                    0
% 23.81/3.48  inst_num_of_dismatching_blockings:      13812
% 23.81/3.48  inst_num_of_non_proper_insts:           10151
% 23.81/3.48  inst_num_of_duplicates:                 0
% 23.81/3.48  inst_inst_num_from_inst_to_res:         0
% 23.81/3.48  inst_dismatching_checking_time:         0.
% 23.81/3.48  
% 23.81/3.48  ------ Resolution
% 23.81/3.48  
% 23.81/3.48  res_num_of_clauses:                     0
% 23.81/3.48  res_num_in_passive:                     0
% 23.81/3.48  res_num_in_active:                      0
% 23.81/3.48  res_num_of_loops:                       91
% 23.81/3.48  res_forward_subset_subsumed:            161
% 23.81/3.48  res_backward_subset_subsumed:           0
% 23.81/3.48  res_forward_subsumed:                   0
% 23.81/3.48  res_backward_subsumed:                  0
% 23.81/3.48  res_forward_subsumption_resolution:     0
% 23.81/3.48  res_backward_subsumption_resolution:    0
% 23.81/3.48  res_clause_to_clause_subsumption:       16710
% 23.81/3.48  res_orphan_elimination:                 0
% 23.81/3.48  res_tautology_del:                      387
% 23.81/3.48  res_num_eq_res_simplified:              0
% 23.81/3.48  res_num_sel_changes:                    0
% 23.81/3.48  res_moves_from_active_to_pass:          0
% 23.81/3.48  
% 23.81/3.48  ------ Superposition
% 23.81/3.48  
% 23.81/3.48  sup_time_total:                         0.
% 23.81/3.48  sup_time_generating:                    0.
% 23.81/3.48  sup_time_sim_full:                      0.
% 23.81/3.48  sup_time_sim_immed:                     0.
% 23.81/3.48  
% 23.81/3.48  sup_num_of_clauses:                     3698
% 23.81/3.48  sup_num_in_active:                      400
% 23.81/3.48  sup_num_in_passive:                     3298
% 23.81/3.48  sup_num_of_loops:                       468
% 23.81/3.48  sup_fw_superposition:                   2593
% 23.81/3.48  sup_bw_superposition:                   4108
% 23.81/3.48  sup_immediate_simplified:               1788
% 23.81/3.48  sup_given_eliminated:                   0
% 23.81/3.48  comparisons_done:                       0
% 23.81/3.48  comparisons_avoided:                    0
% 23.81/3.48  
% 23.81/3.48  ------ Simplifications
% 23.81/3.48  
% 23.81/3.48  
% 23.81/3.48  sim_fw_subset_subsumed:                 287
% 23.81/3.48  sim_bw_subset_subsumed:                 189
% 23.81/3.48  sim_fw_subsumed:                        762
% 23.81/3.48  sim_bw_subsumed:                        59
% 23.81/3.48  sim_fw_subsumption_res:                 0
% 23.81/3.48  sim_bw_subsumption_res:                 0
% 23.81/3.48  sim_tautology_del:                      190
% 23.81/3.48  sim_eq_tautology_del:                   455
% 23.81/3.48  sim_eq_res_simp:                        0
% 23.81/3.48  sim_fw_demodulated:                     263
% 23.81/3.48  sim_bw_demodulated:                     17
% 23.81/3.48  sim_light_normalised:                   523
% 23.81/3.48  sim_joinable_taut:                      0
% 23.81/3.48  sim_joinable_simp:                      0
% 23.81/3.48  sim_ac_normalised:                      0
% 23.81/3.48  sim_smt_subsumption:                    0
% 23.81/3.48  
%------------------------------------------------------------------------------
