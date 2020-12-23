%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:11 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 456 expanded)
%              Number of clauses        :   72 ( 182 expanded)
%              Number of leaves         :   13 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1122 expanded)
%              Number of equality atoms :  135 ( 579 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_899,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_904,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_888,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_892,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_888,c_892])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_893,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2960,plain,
    ( k8_relset_1(X0,sK0,sK2,X1) = k10_relat_1(sK2,X1)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_893])).

cnf(c_3380,plain,
    ( k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_904,c_2960])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_902,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1812,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_902])).

cnf(c_6503,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) != iProver_top
    | r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3380,c_1812])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1098,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1291,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_1293,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1291])).

cnf(c_1099,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1547,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_1548,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1547])).

cnf(c_13130,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6503,c_22,c_1293,c_1548])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_905,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13141,plain,
    ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13130,c_905])).

cnf(c_13996,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_13141])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_894,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3141,plain,
    ( k7_relset_1(X0,sK0,sK2,X1) = k9_relat_1(sK2,X1)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_894])).

cnf(c_3500,plain,
    ( k7_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_904,c_3141])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_889,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3758,plain,
    ( k7_relset_1(X0,sK0,sK2,X0) = k2_relset_1(X0,sK0,sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_889])).

cnf(c_5159,plain,
    ( k7_relset_1(k1_relat_1(sK2),sK0,sK2,k1_relat_1(sK2)) = k2_relset_1(k1_relat_1(sK2),sK0,sK2) ),
    inference(superposition,[status(thm)],[c_904,c_3758])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_895,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1688,plain,
    ( k2_relset_1(X0,sK0,sK2) = k2_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_895])).

cnf(c_1747,plain,
    ( k2_relset_1(k1_relat_1(sK2),sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_904,c_1688])).

cnf(c_5160,plain,
    ( k7_relset_1(k1_relat_1(sK2),sK0,sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5159,c_1747])).

cnf(c_9114,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3500,c_5160])).

cnf(c_14001,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13996,c_9114])).

cnf(c_3139,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_888,c_894])).

cnf(c_3756,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_888,c_889])).

cnf(c_1557,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_888,c_895])).

cnf(c_3768,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3756,c_1557])).

cnf(c_4219,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3139,c_3768])).

cnf(c_2958,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_888,c_893])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_896,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2027,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_888,c_896])).

cnf(c_20,negated_conjecture,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1652,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1557,c_20])).

cnf(c_2281,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2027,c_1652])).

cnf(c_3175,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2958,c_2281])).

cnf(c_3176,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3175,c_2958])).

cnf(c_3620,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3176,c_3139])).

cnf(c_4222,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4219,c_3620])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_890,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3800,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_888,c_890])).

cnf(c_3812,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3800,c_2027])).

cnf(c_4798,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3812,c_2958])).

cnf(c_6997,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4222,c_4798])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1038,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1039,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1038])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14001,c_9114,c_6997,c_1293,c_1039,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.81/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/1.02  
% 3.81/1.02  ------  iProver source info
% 3.81/1.02  
% 3.81/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.81/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/1.02  git: non_committed_changes: false
% 3.81/1.02  git: last_make_outside_of_git: false
% 3.81/1.02  
% 3.81/1.02  ------ 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options
% 3.81/1.02  
% 3.81/1.02  --out_options                           all
% 3.81/1.02  --tptp_safe_out                         true
% 3.81/1.02  --problem_path                          ""
% 3.81/1.02  --include_path                          ""
% 3.81/1.02  --clausifier                            res/vclausify_rel
% 3.81/1.02  --clausifier_options                    --mode clausify
% 3.81/1.02  --stdin                                 false
% 3.81/1.02  --stats_out                             all
% 3.81/1.02  
% 3.81/1.02  ------ General Options
% 3.81/1.02  
% 3.81/1.02  --fof                                   false
% 3.81/1.02  --time_out_real                         305.
% 3.81/1.02  --time_out_virtual                      -1.
% 3.81/1.02  --symbol_type_check                     false
% 3.81/1.02  --clausify_out                          false
% 3.81/1.02  --sig_cnt_out                           false
% 3.81/1.02  --trig_cnt_out                          false
% 3.81/1.02  --trig_cnt_out_tolerance                1.
% 3.81/1.02  --trig_cnt_out_sk_spl                   false
% 3.81/1.02  --abstr_cl_out                          false
% 3.81/1.02  
% 3.81/1.02  ------ Global Options
% 3.81/1.02  
% 3.81/1.02  --schedule                              default
% 3.81/1.02  --add_important_lit                     false
% 3.81/1.02  --prop_solver_per_cl                    1000
% 3.81/1.02  --min_unsat_core                        false
% 3.81/1.02  --soft_assumptions                      false
% 3.81/1.02  --soft_lemma_size                       3
% 3.81/1.02  --prop_impl_unit_size                   0
% 3.81/1.02  --prop_impl_unit                        []
% 3.81/1.02  --share_sel_clauses                     true
% 3.81/1.02  --reset_solvers                         false
% 3.81/1.02  --bc_imp_inh                            [conj_cone]
% 3.81/1.02  --conj_cone_tolerance                   3.
% 3.81/1.02  --extra_neg_conj                        none
% 3.81/1.02  --large_theory_mode                     true
% 3.81/1.02  --prolific_symb_bound                   200
% 3.81/1.02  --lt_threshold                          2000
% 3.81/1.02  --clause_weak_htbl                      true
% 3.81/1.02  --gc_record_bc_elim                     false
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing Options
% 3.81/1.02  
% 3.81/1.02  --preprocessing_flag                    true
% 3.81/1.02  --time_out_prep_mult                    0.1
% 3.81/1.02  --splitting_mode                        input
% 3.81/1.02  --splitting_grd                         true
% 3.81/1.02  --splitting_cvd                         false
% 3.81/1.02  --splitting_cvd_svl                     false
% 3.81/1.02  --splitting_nvd                         32
% 3.81/1.02  --sub_typing                            true
% 3.81/1.02  --prep_gs_sim                           true
% 3.81/1.02  --prep_unflatten                        true
% 3.81/1.02  --prep_res_sim                          true
% 3.81/1.02  --prep_upred                            true
% 3.81/1.02  --prep_sem_filter                       exhaustive
% 3.81/1.02  --prep_sem_filter_out                   false
% 3.81/1.02  --pred_elim                             true
% 3.81/1.02  --res_sim_input                         true
% 3.81/1.02  --eq_ax_congr_red                       true
% 3.81/1.02  --pure_diseq_elim                       true
% 3.81/1.02  --brand_transform                       false
% 3.81/1.02  --non_eq_to_eq                          false
% 3.81/1.02  --prep_def_merge                        true
% 3.81/1.02  --prep_def_merge_prop_impl              false
% 3.81/1.02  --prep_def_merge_mbd                    true
% 3.81/1.02  --prep_def_merge_tr_red                 false
% 3.81/1.02  --prep_def_merge_tr_cl                  false
% 3.81/1.02  --smt_preprocessing                     true
% 3.81/1.02  --smt_ac_axioms                         fast
% 3.81/1.02  --preprocessed_out                      false
% 3.81/1.02  --preprocessed_stats                    false
% 3.81/1.02  
% 3.81/1.02  ------ Abstraction refinement Options
% 3.81/1.02  
% 3.81/1.02  --abstr_ref                             []
% 3.81/1.02  --abstr_ref_prep                        false
% 3.81/1.02  --abstr_ref_until_sat                   false
% 3.81/1.02  --abstr_ref_sig_restrict                funpre
% 3.81/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.02  --abstr_ref_under                       []
% 3.81/1.02  
% 3.81/1.02  ------ SAT Options
% 3.81/1.02  
% 3.81/1.02  --sat_mode                              false
% 3.81/1.02  --sat_fm_restart_options                ""
% 3.81/1.02  --sat_gr_def                            false
% 3.81/1.02  --sat_epr_types                         true
% 3.81/1.02  --sat_non_cyclic_types                  false
% 3.81/1.02  --sat_finite_models                     false
% 3.81/1.02  --sat_fm_lemmas                         false
% 3.81/1.02  --sat_fm_prep                           false
% 3.81/1.02  --sat_fm_uc_incr                        true
% 3.81/1.02  --sat_out_model                         small
% 3.81/1.02  --sat_out_clauses                       false
% 3.81/1.02  
% 3.81/1.02  ------ QBF Options
% 3.81/1.02  
% 3.81/1.02  --qbf_mode                              false
% 3.81/1.02  --qbf_elim_univ                         false
% 3.81/1.02  --qbf_dom_inst                          none
% 3.81/1.02  --qbf_dom_pre_inst                      false
% 3.81/1.02  --qbf_sk_in                             false
% 3.81/1.02  --qbf_pred_elim                         true
% 3.81/1.02  --qbf_split                             512
% 3.81/1.02  
% 3.81/1.02  ------ BMC1 Options
% 3.81/1.02  
% 3.81/1.02  --bmc1_incremental                      false
% 3.81/1.02  --bmc1_axioms                           reachable_all
% 3.81/1.02  --bmc1_min_bound                        0
% 3.81/1.02  --bmc1_max_bound                        -1
% 3.81/1.02  --bmc1_max_bound_default                -1
% 3.81/1.02  --bmc1_symbol_reachability              true
% 3.81/1.02  --bmc1_property_lemmas                  false
% 3.81/1.02  --bmc1_k_induction                      false
% 3.81/1.02  --bmc1_non_equiv_states                 false
% 3.81/1.02  --bmc1_deadlock                         false
% 3.81/1.02  --bmc1_ucm                              false
% 3.81/1.02  --bmc1_add_unsat_core                   none
% 3.81/1.02  --bmc1_unsat_core_children              false
% 3.81/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.02  --bmc1_out_stat                         full
% 3.81/1.02  --bmc1_ground_init                      false
% 3.81/1.02  --bmc1_pre_inst_next_state              false
% 3.81/1.02  --bmc1_pre_inst_state                   false
% 3.81/1.02  --bmc1_pre_inst_reach_state             false
% 3.81/1.02  --bmc1_out_unsat_core                   false
% 3.81/1.02  --bmc1_aig_witness_out                  false
% 3.81/1.02  --bmc1_verbose                          false
% 3.81/1.02  --bmc1_dump_clauses_tptp                false
% 3.81/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.02  --bmc1_dump_file                        -
% 3.81/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.02  --bmc1_ucm_extend_mode                  1
% 3.81/1.02  --bmc1_ucm_init_mode                    2
% 3.81/1.02  --bmc1_ucm_cone_mode                    none
% 3.81/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.02  --bmc1_ucm_relax_model                  4
% 3.81/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.02  --bmc1_ucm_layered_model                none
% 3.81/1.02  --bmc1_ucm_max_lemma_size               10
% 3.81/1.02  
% 3.81/1.02  ------ AIG Options
% 3.81/1.02  
% 3.81/1.02  --aig_mode                              false
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation Options
% 3.81/1.02  
% 3.81/1.02  --instantiation_flag                    true
% 3.81/1.02  --inst_sos_flag                         false
% 3.81/1.02  --inst_sos_phase                        true
% 3.81/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel_side                     num_symb
% 3.81/1.02  --inst_solver_per_active                1400
% 3.81/1.02  --inst_solver_calls_frac                1.
% 3.81/1.02  --inst_passive_queue_type               priority_queues
% 3.81/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.02  --inst_passive_queues_freq              [25;2]
% 3.81/1.02  --inst_dismatching                      true
% 3.81/1.02  --inst_eager_unprocessed_to_passive     true
% 3.81/1.02  --inst_prop_sim_given                   true
% 3.81/1.02  --inst_prop_sim_new                     false
% 3.81/1.02  --inst_subs_new                         false
% 3.81/1.02  --inst_eq_res_simp                      false
% 3.81/1.02  --inst_subs_given                       false
% 3.81/1.02  --inst_orphan_elimination               true
% 3.81/1.02  --inst_learning_loop_flag               true
% 3.81/1.02  --inst_learning_start                   3000
% 3.81/1.02  --inst_learning_factor                  2
% 3.81/1.02  --inst_start_prop_sim_after_learn       3
% 3.81/1.02  --inst_sel_renew                        solver
% 3.81/1.02  --inst_lit_activity_flag                true
% 3.81/1.02  --inst_restr_to_given                   false
% 3.81/1.02  --inst_activity_threshold               500
% 3.81/1.02  --inst_out_proof                        true
% 3.81/1.02  
% 3.81/1.02  ------ Resolution Options
% 3.81/1.02  
% 3.81/1.02  --resolution_flag                       true
% 3.81/1.02  --res_lit_sel                           adaptive
% 3.81/1.02  --res_lit_sel_side                      none
% 3.81/1.02  --res_ordering                          kbo
% 3.81/1.02  --res_to_prop_solver                    active
% 3.81/1.02  --res_prop_simpl_new                    false
% 3.81/1.02  --res_prop_simpl_given                  true
% 3.81/1.02  --res_passive_queue_type                priority_queues
% 3.81/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.02  --res_passive_queues_freq               [15;5]
% 3.81/1.02  --res_forward_subs                      full
% 3.81/1.02  --res_backward_subs                     full
% 3.81/1.02  --res_forward_subs_resolution           true
% 3.81/1.02  --res_backward_subs_resolution          true
% 3.81/1.02  --res_orphan_elimination                true
% 3.81/1.02  --res_time_limit                        2.
% 3.81/1.02  --res_out_proof                         true
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Options
% 3.81/1.02  
% 3.81/1.02  --superposition_flag                    true
% 3.81/1.02  --sup_passive_queue_type                priority_queues
% 3.81/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.02  --demod_completeness_check              fast
% 3.81/1.02  --demod_use_ground                      true
% 3.81/1.02  --sup_to_prop_solver                    passive
% 3.81/1.02  --sup_prop_simpl_new                    true
% 3.81/1.02  --sup_prop_simpl_given                  true
% 3.81/1.02  --sup_fun_splitting                     false
% 3.81/1.02  --sup_smt_interval                      50000
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Simplification Setup
% 3.81/1.02  
% 3.81/1.02  --sup_indices_passive                   []
% 3.81/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_full_bw                           [BwDemod]
% 3.81/1.02  --sup_immed_triv                        [TrivRules]
% 3.81/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_immed_bw_main                     []
% 3.81/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.02  
% 3.81/1.02  ------ Combination Options
% 3.81/1.02  
% 3.81/1.02  --comb_res_mult                         3
% 3.81/1.02  --comb_sup_mult                         2
% 3.81/1.02  --comb_inst_mult                        10
% 3.81/1.02  
% 3.81/1.02  ------ Debug Options
% 3.81/1.02  
% 3.81/1.02  --dbg_backtrace                         false
% 3.81/1.02  --dbg_dump_prop_clauses                 false
% 3.81/1.02  --dbg_dump_prop_clauses_file            -
% 3.81/1.02  --dbg_out_stat                          false
% 3.81/1.02  ------ Parsing...
% 3.81/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.02  ------ Proving...
% 3.81/1.02  ------ Problem Properties 
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  clauses                                 21
% 3.81/1.02  conjectures                             2
% 3.81/1.02  EPR                                     2
% 3.81/1.02  Horn                                    21
% 3.81/1.02  unary                                   5
% 3.81/1.02  binary                                  11
% 3.81/1.02  lits                                    42
% 3.81/1.02  lits eq                                 13
% 3.81/1.02  fd_pure                                 0
% 3.81/1.02  fd_pseudo                               0
% 3.81/1.02  fd_cond                                 0
% 3.81/1.02  fd_pseudo_cond                          1
% 3.81/1.02  AC symbols                              0
% 3.81/1.02  
% 3.81/1.02  ------ Schedule dynamic 5 is on 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  ------ 
% 3.81/1.02  Current options:
% 3.81/1.02  ------ 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options
% 3.81/1.02  
% 3.81/1.02  --out_options                           all
% 3.81/1.02  --tptp_safe_out                         true
% 3.81/1.02  --problem_path                          ""
% 3.81/1.02  --include_path                          ""
% 3.81/1.02  --clausifier                            res/vclausify_rel
% 3.81/1.02  --clausifier_options                    --mode clausify
% 3.81/1.02  --stdin                                 false
% 3.81/1.02  --stats_out                             all
% 3.81/1.02  
% 3.81/1.02  ------ General Options
% 3.81/1.02  
% 3.81/1.02  --fof                                   false
% 3.81/1.02  --time_out_real                         305.
% 3.81/1.02  --time_out_virtual                      -1.
% 3.81/1.02  --symbol_type_check                     false
% 3.81/1.02  --clausify_out                          false
% 3.81/1.02  --sig_cnt_out                           false
% 3.81/1.02  --trig_cnt_out                          false
% 3.81/1.02  --trig_cnt_out_tolerance                1.
% 3.81/1.02  --trig_cnt_out_sk_spl                   false
% 3.81/1.02  --abstr_cl_out                          false
% 3.81/1.02  
% 3.81/1.02  ------ Global Options
% 3.81/1.02  
% 3.81/1.02  --schedule                              default
% 3.81/1.02  --add_important_lit                     false
% 3.81/1.02  --prop_solver_per_cl                    1000
% 3.81/1.02  --min_unsat_core                        false
% 3.81/1.02  --soft_assumptions                      false
% 3.81/1.02  --soft_lemma_size                       3
% 3.81/1.02  --prop_impl_unit_size                   0
% 3.81/1.02  --prop_impl_unit                        []
% 3.81/1.02  --share_sel_clauses                     true
% 3.81/1.02  --reset_solvers                         false
% 3.81/1.02  --bc_imp_inh                            [conj_cone]
% 3.81/1.02  --conj_cone_tolerance                   3.
% 3.81/1.02  --extra_neg_conj                        none
% 3.81/1.02  --large_theory_mode                     true
% 3.81/1.02  --prolific_symb_bound                   200
% 3.81/1.02  --lt_threshold                          2000
% 3.81/1.02  --clause_weak_htbl                      true
% 3.81/1.02  --gc_record_bc_elim                     false
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing Options
% 3.81/1.02  
% 3.81/1.02  --preprocessing_flag                    true
% 3.81/1.02  --time_out_prep_mult                    0.1
% 3.81/1.02  --splitting_mode                        input
% 3.81/1.02  --splitting_grd                         true
% 3.81/1.02  --splitting_cvd                         false
% 3.81/1.02  --splitting_cvd_svl                     false
% 3.81/1.02  --splitting_nvd                         32
% 3.81/1.02  --sub_typing                            true
% 3.81/1.02  --prep_gs_sim                           true
% 3.81/1.02  --prep_unflatten                        true
% 3.81/1.02  --prep_res_sim                          true
% 3.81/1.02  --prep_upred                            true
% 3.81/1.02  --prep_sem_filter                       exhaustive
% 3.81/1.02  --prep_sem_filter_out                   false
% 3.81/1.02  --pred_elim                             true
% 3.81/1.02  --res_sim_input                         true
% 3.81/1.02  --eq_ax_congr_red                       true
% 3.81/1.02  --pure_diseq_elim                       true
% 3.81/1.02  --brand_transform                       false
% 3.81/1.02  --non_eq_to_eq                          false
% 3.81/1.02  --prep_def_merge                        true
% 3.81/1.02  --prep_def_merge_prop_impl              false
% 3.81/1.02  --prep_def_merge_mbd                    true
% 3.81/1.02  --prep_def_merge_tr_red                 false
% 3.81/1.02  --prep_def_merge_tr_cl                  false
% 3.81/1.02  --smt_preprocessing                     true
% 3.81/1.02  --smt_ac_axioms                         fast
% 3.81/1.02  --preprocessed_out                      false
% 3.81/1.02  --preprocessed_stats                    false
% 3.81/1.02  
% 3.81/1.02  ------ Abstraction refinement Options
% 3.81/1.02  
% 3.81/1.02  --abstr_ref                             []
% 3.81/1.02  --abstr_ref_prep                        false
% 3.81/1.02  --abstr_ref_until_sat                   false
% 3.81/1.02  --abstr_ref_sig_restrict                funpre
% 3.81/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.02  --abstr_ref_under                       []
% 3.81/1.02  
% 3.81/1.02  ------ SAT Options
% 3.81/1.02  
% 3.81/1.02  --sat_mode                              false
% 3.81/1.02  --sat_fm_restart_options                ""
% 3.81/1.02  --sat_gr_def                            false
% 3.81/1.02  --sat_epr_types                         true
% 3.81/1.02  --sat_non_cyclic_types                  false
% 3.81/1.02  --sat_finite_models                     false
% 3.81/1.02  --sat_fm_lemmas                         false
% 3.81/1.02  --sat_fm_prep                           false
% 3.81/1.02  --sat_fm_uc_incr                        true
% 3.81/1.02  --sat_out_model                         small
% 3.81/1.02  --sat_out_clauses                       false
% 3.81/1.02  
% 3.81/1.02  ------ QBF Options
% 3.81/1.02  
% 3.81/1.02  --qbf_mode                              false
% 3.81/1.02  --qbf_elim_univ                         false
% 3.81/1.02  --qbf_dom_inst                          none
% 3.81/1.02  --qbf_dom_pre_inst                      false
% 3.81/1.02  --qbf_sk_in                             false
% 3.81/1.02  --qbf_pred_elim                         true
% 3.81/1.02  --qbf_split                             512
% 3.81/1.02  
% 3.81/1.02  ------ BMC1 Options
% 3.81/1.02  
% 3.81/1.02  --bmc1_incremental                      false
% 3.81/1.02  --bmc1_axioms                           reachable_all
% 3.81/1.02  --bmc1_min_bound                        0
% 3.81/1.02  --bmc1_max_bound                        -1
% 3.81/1.02  --bmc1_max_bound_default                -1
% 3.81/1.02  --bmc1_symbol_reachability              true
% 3.81/1.02  --bmc1_property_lemmas                  false
% 3.81/1.02  --bmc1_k_induction                      false
% 3.81/1.02  --bmc1_non_equiv_states                 false
% 3.81/1.02  --bmc1_deadlock                         false
% 3.81/1.02  --bmc1_ucm                              false
% 3.81/1.02  --bmc1_add_unsat_core                   none
% 3.81/1.02  --bmc1_unsat_core_children              false
% 3.81/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.02  --bmc1_out_stat                         full
% 3.81/1.02  --bmc1_ground_init                      false
% 3.81/1.02  --bmc1_pre_inst_next_state              false
% 3.81/1.02  --bmc1_pre_inst_state                   false
% 3.81/1.02  --bmc1_pre_inst_reach_state             false
% 3.81/1.02  --bmc1_out_unsat_core                   false
% 3.81/1.02  --bmc1_aig_witness_out                  false
% 3.81/1.02  --bmc1_verbose                          false
% 3.81/1.02  --bmc1_dump_clauses_tptp                false
% 3.81/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.02  --bmc1_dump_file                        -
% 3.81/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.02  --bmc1_ucm_extend_mode                  1
% 3.81/1.02  --bmc1_ucm_init_mode                    2
% 3.81/1.02  --bmc1_ucm_cone_mode                    none
% 3.81/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.02  --bmc1_ucm_relax_model                  4
% 3.81/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.02  --bmc1_ucm_layered_model                none
% 3.81/1.02  --bmc1_ucm_max_lemma_size               10
% 3.81/1.02  
% 3.81/1.02  ------ AIG Options
% 3.81/1.02  
% 3.81/1.02  --aig_mode                              false
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation Options
% 3.81/1.02  
% 3.81/1.02  --instantiation_flag                    true
% 3.81/1.02  --inst_sos_flag                         false
% 3.81/1.02  --inst_sos_phase                        true
% 3.81/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel_side                     none
% 3.81/1.02  --inst_solver_per_active                1400
% 3.81/1.02  --inst_solver_calls_frac                1.
% 3.81/1.02  --inst_passive_queue_type               priority_queues
% 3.81/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.02  --inst_passive_queues_freq              [25;2]
% 3.81/1.02  --inst_dismatching                      true
% 3.81/1.02  --inst_eager_unprocessed_to_passive     true
% 3.81/1.02  --inst_prop_sim_given                   true
% 3.81/1.02  --inst_prop_sim_new                     false
% 3.81/1.02  --inst_subs_new                         false
% 3.81/1.02  --inst_eq_res_simp                      false
% 3.81/1.02  --inst_subs_given                       false
% 3.81/1.02  --inst_orphan_elimination               true
% 3.81/1.02  --inst_learning_loop_flag               true
% 3.81/1.02  --inst_learning_start                   3000
% 3.81/1.02  --inst_learning_factor                  2
% 3.81/1.02  --inst_start_prop_sim_after_learn       3
% 3.81/1.02  --inst_sel_renew                        solver
% 3.81/1.02  --inst_lit_activity_flag                true
% 3.81/1.02  --inst_restr_to_given                   false
% 3.81/1.02  --inst_activity_threshold               500
% 3.81/1.02  --inst_out_proof                        true
% 3.81/1.02  
% 3.81/1.02  ------ Resolution Options
% 3.81/1.02  
% 3.81/1.02  --resolution_flag                       false
% 3.81/1.02  --res_lit_sel                           adaptive
% 3.81/1.02  --res_lit_sel_side                      none
% 3.81/1.02  --res_ordering                          kbo
% 3.81/1.02  --res_to_prop_solver                    active
% 3.81/1.02  --res_prop_simpl_new                    false
% 3.81/1.02  --res_prop_simpl_given                  true
% 3.81/1.02  --res_passive_queue_type                priority_queues
% 3.81/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.02  --res_passive_queues_freq               [15;5]
% 3.81/1.02  --res_forward_subs                      full
% 3.81/1.02  --res_backward_subs                     full
% 3.81/1.02  --res_forward_subs_resolution           true
% 3.81/1.02  --res_backward_subs_resolution          true
% 3.81/1.02  --res_orphan_elimination                true
% 3.81/1.02  --res_time_limit                        2.
% 3.81/1.02  --res_out_proof                         true
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Options
% 3.81/1.02  
% 3.81/1.02  --superposition_flag                    true
% 3.81/1.02  --sup_passive_queue_type                priority_queues
% 3.81/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.02  --demod_completeness_check              fast
% 3.81/1.02  --demod_use_ground                      true
% 3.81/1.02  --sup_to_prop_solver                    passive
% 3.81/1.02  --sup_prop_simpl_new                    true
% 3.81/1.02  --sup_prop_simpl_given                  true
% 3.81/1.02  --sup_fun_splitting                     false
% 3.81/1.02  --sup_smt_interval                      50000
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Simplification Setup
% 3.81/1.02  
% 3.81/1.02  --sup_indices_passive                   []
% 3.81/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_full_bw                           [BwDemod]
% 3.81/1.02  --sup_immed_triv                        [TrivRules]
% 3.81/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_immed_bw_main                     []
% 3.81/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.02  
% 3.81/1.02  ------ Combination Options
% 3.81/1.02  
% 3.81/1.02  --comb_res_mult                         3
% 3.81/1.02  --comb_sup_mult                         2
% 3.81/1.02  --comb_inst_mult                        10
% 3.81/1.02  
% 3.81/1.02  ------ Debug Options
% 3.81/1.02  
% 3.81/1.02  --dbg_backtrace                         false
% 3.81/1.02  --dbg_dump_prop_clauses                 false
% 3.81/1.02  --dbg_dump_prop_clauses_file            -
% 3.81/1.02  --dbg_out_stat                          false
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  ------ Proving...
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  % SZS status Theorem for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  fof(f6,axiom,(
% 3.81/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f21,plain,(
% 3.81/1.02    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.81/1.02    inference(ennf_transformation,[],[f6])).
% 3.81/1.02  
% 3.81/1.02  fof(f22,plain,(
% 3.81/1.02    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.81/1.02    inference(flattening,[],[f21])).
% 3.81/1.02  
% 3.81/1.02  fof(f47,plain,(
% 3.81/1.02    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f22])).
% 3.81/1.02  
% 3.81/1.02  fof(f1,axiom,(
% 3.81/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f33,plain,(
% 3.81/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.81/1.02    inference(nnf_transformation,[],[f1])).
% 3.81/1.02  
% 3.81/1.02  fof(f34,plain,(
% 3.81/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.81/1.02    inference(flattening,[],[f33])).
% 3.81/1.02  
% 3.81/1.02  fof(f39,plain,(
% 3.81/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.81/1.02    inference(cnf_transformation,[],[f34])).
% 3.81/1.02  
% 3.81/1.02  fof(f60,plain,(
% 3.81/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.81/1.02    inference(equality_resolution,[],[f39])).
% 3.81/1.02  
% 3.81/1.02  fof(f16,conjecture,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f17,negated_conjecture,(
% 3.81/1.02    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.81/1.02    inference(negated_conjecture,[],[f16])).
% 3.81/1.02  
% 3.81/1.02  fof(f32,plain,(
% 3.81/1.02    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.81/1.02    inference(ennf_transformation,[],[f17])).
% 3.81/1.02  
% 3.81/1.02  fof(f36,plain,(
% 3.81/1.02    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f37,plain,(
% 3.81/1.02    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.81/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f36])).
% 3.81/1.02  
% 3.81/1.02  fof(f58,plain,(
% 3.81/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.81/1.02    inference(cnf_transformation,[],[f37])).
% 3.81/1.02  
% 3.81/1.02  fof(f13,axiom,(
% 3.81/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f29,plain,(
% 3.81/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.81/1.02    inference(ennf_transformation,[],[f13])).
% 3.81/1.02  
% 3.81/1.02  fof(f30,plain,(
% 3.81/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.81/1.02    inference(flattening,[],[f29])).
% 3.81/1.02  
% 3.81/1.02  fof(f54,plain,(
% 3.81/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f30])).
% 3.81/1.02  
% 3.81/1.02  fof(f12,axiom,(
% 3.81/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f28,plain,(
% 3.81/1.02    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.02    inference(ennf_transformation,[],[f12])).
% 3.81/1.02  
% 3.81/1.02  fof(f53,plain,(
% 3.81/1.02    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f28])).
% 3.81/1.02  
% 3.81/1.02  fof(f8,axiom,(
% 3.81/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f24,plain,(
% 3.81/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.02    inference(ennf_transformation,[],[f8])).
% 3.81/1.02  
% 3.81/1.02  fof(f49,plain,(
% 3.81/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f24])).
% 3.81/1.02  
% 3.81/1.02  fof(f2,axiom,(
% 3.81/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f35,plain,(
% 3.81/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.81/1.02    inference(nnf_transformation,[],[f2])).
% 3.81/1.02  
% 3.81/1.02  fof(f41,plain,(
% 3.81/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f40,plain,(
% 3.81/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f34])).
% 3.81/1.02  
% 3.81/1.02  fof(f11,axiom,(
% 3.81/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f27,plain,(
% 3.81/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.02    inference(ennf_transformation,[],[f11])).
% 3.81/1.02  
% 3.81/1.02  fof(f52,plain,(
% 3.81/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f27])).
% 3.81/1.02  
% 3.81/1.02  fof(f15,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f31,plain,(
% 3.81/1.02    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.02    inference(ennf_transformation,[],[f15])).
% 3.81/1.02  
% 3.81/1.02  fof(f56,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f31])).
% 3.81/1.02  
% 3.81/1.02  fof(f10,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f26,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.02    inference(ennf_transformation,[],[f10])).
% 3.81/1.02  
% 3.81/1.02  fof(f51,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f26])).
% 3.81/1.02  
% 3.81/1.02  fof(f9,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f25,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.02    inference(ennf_transformation,[],[f9])).
% 3.81/1.02  
% 3.81/1.02  fof(f50,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f25])).
% 3.81/1.02  
% 3.81/1.02  fof(f59,plain,(
% 3.81/1.02    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 3.81/1.02    inference(cnf_transformation,[],[f37])).
% 3.81/1.02  
% 3.81/1.02  fof(f57,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f31])).
% 3.81/1.02  
% 3.81/1.02  fof(f7,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f23,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.02    inference(ennf_transformation,[],[f7])).
% 3.81/1.02  
% 3.81/1.02  fof(f48,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f23])).
% 3.81/1.02  
% 3.81/1.02  cnf(c_9,plain,
% 3.81/1.02      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 3.81/1.02      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.81/1.02      | ~ v1_relat_1(X1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_899,plain,
% 3.81/1.02      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 3.81/1.02      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 3.81/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1,plain,
% 3.81/1.02      ( r1_tarski(X0,X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_904,plain,
% 3.81/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_21,negated_conjecture,
% 3.81/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.81/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_888,plain,
% 3.81/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_16,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.81/1.02      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.81/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_892,plain,
% 3.81/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.81/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.81/1.02      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1241,plain,
% 3.81/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) = iProver_top
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_888,c_892]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_15,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.81/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_893,plain,
% 3.81/1.02      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.81/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2960,plain,
% 3.81/1.02      ( k8_relset_1(X0,sK0,sK2,X1) = k10_relat_1(sK2,X1)
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_1241,c_893]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3380,plain,
% 3.81/1.02      ( k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_904,c_2960]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_11,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 3.81/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_897,plain,
% 3.81/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.81/1.02      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_902,plain,
% 3.81/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.81/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1812,plain,
% 3.81/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.81/1.02      | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) = iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_897,c_902]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_6503,plain,
% 3.81/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) != iProver_top
% 3.81/1.02      | r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_3380,c_1812]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_22,plain,
% 3.81/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1098,plain,
% 3.81/1.02      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 3.81/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1291,plain,
% 3.81/1.02      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 3.81/1.02      inference(instantiation,[status(thm)],[c_1098]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1293,plain,
% 3.81/1.02      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_1291]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1099,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 3.81/1.02      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 3.81/1.02      inference(instantiation,[status(thm)],[c_16]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1547,plain,
% 3.81/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
% 3.81/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.81/1.02      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 3.81/1.02      inference(instantiation,[status(thm)],[c_1099]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1548,plain,
% 3.81/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) = iProver_top
% 3.81/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_1547]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_13130,plain,
% 3.81/1.02      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
% 3.81/1.02      inference(global_propositional_subsumption,
% 3.81/1.02                [status(thm)],
% 3.81/1.02                [c_6503,c_22,c_1293,c_1548]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_0,plain,
% 3.81/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.81/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_905,plain,
% 3.81/1.02      ( X0 = X1
% 3.81/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.81/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_13141,plain,
% 3.81/1.02      ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_13130,c_905]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_13996,plain,
% 3.81/1.02      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.81/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_899,c_13141]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_14,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.81/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_894,plain,
% 3.81/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.81/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3141,plain,
% 3.81/1.02      ( k7_relset_1(X0,sK0,sK2,X1) = k9_relat_1(sK2,X1)
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_1241,c_894]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3500,plain,
% 3.81/1.02      ( k7_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_904,c_3141]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_19,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_889,plain,
% 3.81/1.02      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.81/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3758,plain,
% 3.81/1.02      ( k7_relset_1(X0,sK0,sK2,X0) = k2_relset_1(X0,sK0,sK2)
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_1241,c_889]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_5159,plain,
% 3.81/1.02      ( k7_relset_1(k1_relat_1(sK2),sK0,sK2,k1_relat_1(sK2)) = k2_relset_1(k1_relat_1(sK2),sK0,sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_904,c_3758]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_13,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_895,plain,
% 3.81/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.81/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1688,plain,
% 3.81/1.02      ( k2_relset_1(X0,sK0,sK2) = k2_relat_1(sK2)
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_1241,c_895]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1747,plain,
% 3.81/1.02      ( k2_relset_1(k1_relat_1(sK2),sK0,sK2) = k2_relat_1(sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_904,c_1688]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_5160,plain,
% 3.81/1.02      ( k7_relset_1(k1_relat_1(sK2),sK0,sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_5159,c_1747]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_9114,plain,
% 3.81/1.02      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_3500,c_5160]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_14001,plain,
% 3.81/1.02      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 3.81/1.02      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.81/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_13996,c_9114]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3139,plain,
% 3.81/1.02      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_888,c_894]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3756,plain,
% 3.81/1.02      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_888,c_889]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1557,plain,
% 3.81/1.02      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_888,c_895]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3768,plain,
% 3.81/1.02      ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_3756,c_1557]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4219,plain,
% 3.81/1.02      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_3139,c_3768]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2958,plain,
% 3.81/1.02      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_888,c_893]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_12,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_896,plain,
% 3.81/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.81/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2027,plain,
% 3.81/1.02      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_888,c_896]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_20,negated_conjecture,
% 3.81/1.02      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 3.81/1.02      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
% 3.81/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1652,plain,
% 3.81/1.02      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 3.81/1.02      | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
% 3.81/1.02      inference(demodulation,[status(thm)],[c_1557,c_20]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2281,plain,
% 3.81/1.02      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 3.81/1.02      | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 3.81/1.02      inference(demodulation,[status(thm)],[c_2027,c_1652]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3175,plain,
% 3.81/1.02      ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
% 3.81/1.02      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 3.81/1.02      inference(demodulation,[status(thm)],[c_2958,c_2281]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3176,plain,
% 3.81/1.02      ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 3.81/1.02      | k10_relat_1(sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
% 3.81/1.02      inference(demodulation,[status(thm)],[c_3175,c_2958]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3620,plain,
% 3.81/1.02      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
% 3.81/1.02      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 3.81/1.02      inference(demodulation,[status(thm)],[c_3176,c_3139]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4222,plain,
% 3.81/1.02      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 3.81/1.02      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 3.81/1.02      inference(demodulation,[status(thm)],[c_4219,c_3620]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_18,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_890,plain,
% 3.81/1.02      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 3.81/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3800,plain,
% 3.81/1.02      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_888,c_890]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3812,plain,
% 3.81/1.02      ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_3800,c_2027]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4798,plain,
% 3.81/1.02      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_3812,c_2958]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_6997,plain,
% 3.81/1.02      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 3.81/1.02      | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_4222,c_4798]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_10,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.02      | v1_relat_1(X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1038,plain,
% 3.81/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.81/1.02      | v1_relat_1(sK2) ),
% 3.81/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1039,plain,
% 3.81/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.81/1.02      | v1_relat_1(sK2) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_1038]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(contradiction,plain,
% 3.81/1.02      ( $false ),
% 3.81/1.02      inference(minisat,
% 3.81/1.02                [status(thm)],
% 3.81/1.02                [c_14001,c_9114,c_6997,c_1293,c_1039,c_22]) ).
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  ------                               Statistics
% 3.81/1.02  
% 3.81/1.02  ------ General
% 3.81/1.02  
% 3.81/1.02  abstr_ref_over_cycles:                  0
% 3.81/1.02  abstr_ref_under_cycles:                 0
% 3.81/1.02  gc_basic_clause_elim:                   0
% 3.81/1.02  forced_gc_time:                         0
% 3.81/1.02  parsing_time:                           0.01
% 3.81/1.02  unif_index_cands_time:                  0.
% 3.81/1.02  unif_index_add_time:                    0.
% 3.81/1.02  orderings_time:                         0.
% 3.81/1.02  out_proof_time:                         0.009
% 3.81/1.02  total_time:                             0.422
% 3.81/1.02  num_of_symbols:                         49
% 3.81/1.02  num_of_terms:                           12893
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing
% 3.81/1.02  
% 3.81/1.02  num_of_splits:                          0
% 3.81/1.02  num_of_split_atoms:                     0
% 3.81/1.02  num_of_reused_defs:                     0
% 3.81/1.02  num_eq_ax_congr_red:                    15
% 3.81/1.02  num_of_sem_filtered_clauses:            1
% 3.81/1.02  num_of_subtypes:                        0
% 3.81/1.02  monotx_restored_types:                  0
% 3.81/1.02  sat_num_of_epr_types:                   0
% 3.81/1.02  sat_num_of_non_cyclic_types:            0
% 3.81/1.02  sat_guarded_non_collapsed_types:        0
% 3.81/1.02  num_pure_diseq_elim:                    0
% 3.81/1.02  simp_replaced_by:                       0
% 3.81/1.02  res_preprocessed:                       115
% 3.81/1.02  prep_upred:                             0
% 3.81/1.02  prep_unflattend:                        0
% 3.81/1.02  smt_new_axioms:                         0
% 3.81/1.02  pred_elim_cands:                        3
% 3.81/1.02  pred_elim:                              0
% 3.81/1.02  pred_elim_cl:                           0
% 3.81/1.02  pred_elim_cycles:                       2
% 3.81/1.02  merged_defs:                            8
% 3.81/1.02  merged_defs_ncl:                        0
% 3.81/1.02  bin_hyper_res:                          8
% 3.81/1.02  prep_cycles:                            4
% 3.81/1.02  pred_elim_time:                         0.001
% 3.81/1.02  splitting_time:                         0.
% 3.81/1.02  sem_filter_time:                        0.
% 3.81/1.02  monotx_time:                            0.
% 3.81/1.02  subtype_inf_time:                       0.
% 3.81/1.02  
% 3.81/1.02  ------ Problem properties
% 3.81/1.02  
% 3.81/1.02  clauses:                                21
% 3.81/1.02  conjectures:                            2
% 3.81/1.02  epr:                                    2
% 3.81/1.02  horn:                                   21
% 3.81/1.02  ground:                                 2
% 3.81/1.02  unary:                                  5
% 3.81/1.02  binary:                                 11
% 3.81/1.02  lits:                                   42
% 3.81/1.02  lits_eq:                                13
% 3.81/1.02  fd_pure:                                0
% 3.81/1.02  fd_pseudo:                              0
% 3.81/1.02  fd_cond:                                0
% 3.81/1.02  fd_pseudo_cond:                         1
% 3.81/1.02  ac_symbols:                             0
% 3.81/1.02  
% 3.81/1.02  ------ Propositional Solver
% 3.81/1.02  
% 3.81/1.02  prop_solver_calls:                      30
% 3.81/1.02  prop_fast_solver_calls:                 824
% 3.81/1.02  smt_solver_calls:                       0
% 3.81/1.02  smt_fast_solver_calls:                  0
% 3.81/1.02  prop_num_of_clauses:                    6515
% 3.81/1.02  prop_preprocess_simplified:             12454
% 3.81/1.02  prop_fo_subsumed:                       17
% 3.81/1.02  prop_solver_time:                       0.
% 3.81/1.02  smt_solver_time:                        0.
% 3.81/1.02  smt_fast_solver_time:                   0.
% 3.81/1.02  prop_fast_solver_time:                  0.
% 3.81/1.02  prop_unsat_core_time:                   0.
% 3.81/1.02  
% 3.81/1.02  ------ QBF
% 3.81/1.02  
% 3.81/1.02  qbf_q_res:                              0
% 3.81/1.02  qbf_num_tautologies:                    0
% 3.81/1.02  qbf_prep_cycles:                        0
% 3.81/1.02  
% 3.81/1.02  ------ BMC1
% 3.81/1.02  
% 3.81/1.02  bmc1_current_bound:                     -1
% 3.81/1.02  bmc1_last_solved_bound:                 -1
% 3.81/1.02  bmc1_unsat_core_size:                   -1
% 3.81/1.02  bmc1_unsat_core_parents_size:           -1
% 3.81/1.02  bmc1_merge_next_fun:                    0
% 3.81/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation
% 3.81/1.02  
% 3.81/1.02  inst_num_of_clauses:                    2132
% 3.81/1.02  inst_num_in_passive:                    522
% 3.81/1.02  inst_num_in_active:                     747
% 3.81/1.02  inst_num_in_unprocessed:                863
% 3.81/1.02  inst_num_of_loops:                      770
% 3.81/1.02  inst_num_of_learning_restarts:          0
% 3.81/1.02  inst_num_moves_active_passive:          20
% 3.81/1.02  inst_lit_activity:                      0
% 3.81/1.02  inst_lit_activity_moves:                0
% 3.81/1.02  inst_num_tautologies:                   0
% 3.81/1.02  inst_num_prop_implied:                  0
% 3.81/1.02  inst_num_existing_simplified:           0
% 3.81/1.02  inst_num_eq_res_simplified:             0
% 3.81/1.02  inst_num_child_elim:                    0
% 3.81/1.02  inst_num_of_dismatching_blockings:      952
% 3.81/1.02  inst_num_of_non_proper_insts:           2284
% 3.81/1.02  inst_num_of_duplicates:                 0
% 3.81/1.02  inst_inst_num_from_inst_to_res:         0
% 3.81/1.02  inst_dismatching_checking_time:         0.
% 3.81/1.02  
% 3.81/1.02  ------ Resolution
% 3.81/1.02  
% 3.81/1.02  res_num_of_clauses:                     0
% 3.81/1.02  res_num_in_passive:                     0
% 3.81/1.02  res_num_in_active:                      0
% 3.81/1.02  res_num_of_loops:                       119
% 3.81/1.02  res_forward_subset_subsumed:            144
% 3.81/1.02  res_backward_subset_subsumed:           4
% 3.81/1.02  res_forward_subsumed:                   0
% 3.81/1.02  res_backward_subsumed:                  0
% 3.81/1.02  res_forward_subsumption_resolution:     0
% 3.81/1.02  res_backward_subsumption_resolution:    0
% 3.81/1.02  res_clause_to_clause_subsumption:       729
% 3.81/1.02  res_orphan_elimination:                 0
% 3.81/1.02  res_tautology_del:                      150
% 3.81/1.02  res_num_eq_res_simplified:              0
% 3.81/1.02  res_num_sel_changes:                    0
% 3.81/1.02  res_moves_from_active_to_pass:          0
% 3.81/1.02  
% 3.81/1.02  ------ Superposition
% 3.81/1.02  
% 3.81/1.02  sup_time_total:                         0.
% 3.81/1.02  sup_time_generating:                    0.
% 3.81/1.02  sup_time_sim_full:                      0.
% 3.81/1.02  sup_time_sim_immed:                     0.
% 3.81/1.02  
% 3.81/1.02  sup_num_of_clauses:                     254
% 3.81/1.02  sup_num_in_active:                      149
% 3.81/1.02  sup_num_in_passive:                     105
% 3.81/1.02  sup_num_of_loops:                       153
% 3.81/1.02  sup_fw_superposition:                   182
% 3.81/1.02  sup_bw_superposition:                   125
% 3.81/1.02  sup_immediate_simplified:               41
% 3.81/1.02  sup_given_eliminated:                   0
% 3.81/1.02  comparisons_done:                       0
% 3.81/1.02  comparisons_avoided:                    0
% 3.81/1.02  
% 3.81/1.02  ------ Simplifications
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  sim_fw_subset_subsumed:                 8
% 3.81/1.02  sim_bw_subset_subsumed:                 2
% 3.81/1.02  sim_fw_subsumed:                        9
% 3.81/1.02  sim_bw_subsumed:                        0
% 3.81/1.02  sim_fw_subsumption_res:                 1
% 3.81/1.02  sim_bw_subsumption_res:                 0
% 3.81/1.02  sim_tautology_del:                      1
% 3.81/1.02  sim_eq_tautology_del:                   5
% 3.81/1.02  sim_eq_res_simp:                        1
% 3.81/1.02  sim_fw_demodulated:                     10
% 3.81/1.02  sim_bw_demodulated:                     5
% 3.81/1.02  sim_light_normalised:                   24
% 3.81/1.02  sim_joinable_taut:                      0
% 3.81/1.02  sim_joinable_simp:                      0
% 3.81/1.02  sim_ac_normalised:                      0
% 3.81/1.02  sim_smt_subsumption:                    0
% 3.81/1.02  
%------------------------------------------------------------------------------
