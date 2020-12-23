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
% DateTime   : Thu Dec  3 11:56:14 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 485 expanded)
%              Number of clauses        :   80 ( 222 expanded)
%              Number of leaves         :   18 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  306 (1224 expanded)
%              Number of equality atoms :  165 ( 573 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_273,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_274,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_684,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_462,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_792,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_787,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_893,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_894,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_893])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_985,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_986,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_1210,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_684,c_792,c_894,c_986])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_691,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_685,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1601,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_685])).

cnf(c_1957,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1210,c_1601])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_688,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1512,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1210,c_688])).

cnf(c_2286,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1957,c_1512])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_11])).

cnf(c_303,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_236,c_20])).

cnf(c_304,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_682,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_967,plain,
    ( k7_relat_1(sK2,sK1) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_682])).

cnf(c_968,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK1) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_967])).

cnf(c_1454,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_967,c_792,c_893,c_968,c_985])).

cnf(c_1684,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1454,c_1512])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_345,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_346,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_840,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_346])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_336,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_337,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_803,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_337])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_855,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_803,c_19])).

cnf(c_881,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_840,c_855])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_318,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_319,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_843,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_319])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_327,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_328,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_852,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_328])).

cnf(c_1320,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_881,c_843,c_852])).

cnf(c_1746,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1684,c_1320])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_686,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1215,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1210,c_686])).

cnf(c_1747,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1746,c_1215])).

cnf(c_1748,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_1747])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_6])).

cnf(c_288,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_20])).

cnf(c_289,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_683,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_290,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_1310,plain,
    ( r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_290,c_792,c_894,c_986])).

cnf(c_1311,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1310])).

cnf(c_1318,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1311])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_690,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1386,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1318,c_690])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_687,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1523,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1210,c_687])).

cnf(c_1750,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1386,c_1523])).

cnf(c_1751,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1750,c_1215])).

cnf(c_1867,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1748,c_1751])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2286,c_1867])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:05:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.99/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/0.97  
% 1.99/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.97  
% 1.99/0.97  ------  iProver source info
% 1.99/0.97  
% 1.99/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.97  git: non_committed_changes: false
% 1.99/0.97  git: last_make_outside_of_git: false
% 1.99/0.97  
% 1.99/0.97  ------ 
% 1.99/0.97  
% 1.99/0.97  ------ Input Options
% 1.99/0.97  
% 1.99/0.97  --out_options                           all
% 1.99/0.97  --tptp_safe_out                         true
% 1.99/0.97  --problem_path                          ""
% 1.99/0.97  --include_path                          ""
% 1.99/0.97  --clausifier                            res/vclausify_rel
% 1.99/0.97  --clausifier_options                    --mode clausify
% 1.99/0.97  --stdin                                 false
% 1.99/0.97  --stats_out                             all
% 1.99/0.97  
% 1.99/0.97  ------ General Options
% 1.99/0.97  
% 1.99/0.97  --fof                                   false
% 1.99/0.97  --time_out_real                         305.
% 1.99/0.97  --time_out_virtual                      -1.
% 1.99/0.97  --symbol_type_check                     false
% 1.99/0.97  --clausify_out                          false
% 1.99/0.97  --sig_cnt_out                           false
% 1.99/0.97  --trig_cnt_out                          false
% 1.99/0.97  --trig_cnt_out_tolerance                1.
% 1.99/0.97  --trig_cnt_out_sk_spl                   false
% 1.99/0.97  --abstr_cl_out                          false
% 1.99/0.97  
% 1.99/0.97  ------ Global Options
% 1.99/0.97  
% 1.99/0.97  --schedule                              default
% 1.99/0.97  --add_important_lit                     false
% 1.99/0.97  --prop_solver_per_cl                    1000
% 1.99/0.97  --min_unsat_core                        false
% 1.99/0.97  --soft_assumptions                      false
% 1.99/0.97  --soft_lemma_size                       3
% 1.99/0.97  --prop_impl_unit_size                   0
% 1.99/0.97  --prop_impl_unit                        []
% 1.99/0.97  --share_sel_clauses                     true
% 1.99/0.97  --reset_solvers                         false
% 1.99/0.97  --bc_imp_inh                            [conj_cone]
% 1.99/0.97  --conj_cone_tolerance                   3.
% 1.99/0.97  --extra_neg_conj                        none
% 1.99/0.97  --large_theory_mode                     true
% 1.99/0.97  --prolific_symb_bound                   200
% 1.99/0.97  --lt_threshold                          2000
% 1.99/0.97  --clause_weak_htbl                      true
% 1.99/0.97  --gc_record_bc_elim                     false
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing Options
% 1.99/0.97  
% 1.99/0.97  --preprocessing_flag                    true
% 1.99/0.97  --time_out_prep_mult                    0.1
% 1.99/0.97  --splitting_mode                        input
% 1.99/0.97  --splitting_grd                         true
% 1.99/0.97  --splitting_cvd                         false
% 1.99/0.97  --splitting_cvd_svl                     false
% 1.99/0.97  --splitting_nvd                         32
% 1.99/0.97  --sub_typing                            true
% 1.99/0.97  --prep_gs_sim                           true
% 1.99/0.97  --prep_unflatten                        true
% 1.99/0.97  --prep_res_sim                          true
% 1.99/0.97  --prep_upred                            true
% 1.99/0.97  --prep_sem_filter                       exhaustive
% 1.99/0.97  --prep_sem_filter_out                   false
% 1.99/0.97  --pred_elim                             true
% 1.99/0.97  --res_sim_input                         true
% 1.99/0.97  --eq_ax_congr_red                       true
% 1.99/0.97  --pure_diseq_elim                       true
% 1.99/0.97  --brand_transform                       false
% 1.99/0.97  --non_eq_to_eq                          false
% 1.99/0.97  --prep_def_merge                        true
% 1.99/0.97  --prep_def_merge_prop_impl              false
% 1.99/0.97  --prep_def_merge_mbd                    true
% 1.99/0.97  --prep_def_merge_tr_red                 false
% 1.99/0.97  --prep_def_merge_tr_cl                  false
% 1.99/0.97  --smt_preprocessing                     true
% 1.99/0.97  --smt_ac_axioms                         fast
% 1.99/0.97  --preprocessed_out                      false
% 1.99/0.97  --preprocessed_stats                    false
% 1.99/0.97  
% 1.99/0.97  ------ Abstraction refinement Options
% 1.99/0.97  
% 1.99/0.97  --abstr_ref                             []
% 1.99/0.97  --abstr_ref_prep                        false
% 1.99/0.97  --abstr_ref_until_sat                   false
% 1.99/0.97  --abstr_ref_sig_restrict                funpre
% 1.99/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.97  --abstr_ref_under                       []
% 1.99/0.97  
% 1.99/0.97  ------ SAT Options
% 1.99/0.97  
% 1.99/0.97  --sat_mode                              false
% 1.99/0.97  --sat_fm_restart_options                ""
% 1.99/0.97  --sat_gr_def                            false
% 1.99/0.97  --sat_epr_types                         true
% 1.99/0.97  --sat_non_cyclic_types                  false
% 1.99/0.97  --sat_finite_models                     false
% 1.99/0.97  --sat_fm_lemmas                         false
% 1.99/0.97  --sat_fm_prep                           false
% 1.99/0.97  --sat_fm_uc_incr                        true
% 1.99/0.97  --sat_out_model                         small
% 1.99/0.97  --sat_out_clauses                       false
% 1.99/0.97  
% 1.99/0.97  ------ QBF Options
% 1.99/0.97  
% 1.99/0.97  --qbf_mode                              false
% 1.99/0.97  --qbf_elim_univ                         false
% 1.99/0.97  --qbf_dom_inst                          none
% 1.99/0.97  --qbf_dom_pre_inst                      false
% 1.99/0.97  --qbf_sk_in                             false
% 1.99/0.97  --qbf_pred_elim                         true
% 1.99/0.97  --qbf_split                             512
% 1.99/0.97  
% 1.99/0.97  ------ BMC1 Options
% 1.99/0.97  
% 1.99/0.97  --bmc1_incremental                      false
% 1.99/0.97  --bmc1_axioms                           reachable_all
% 1.99/0.97  --bmc1_min_bound                        0
% 1.99/0.97  --bmc1_max_bound                        -1
% 1.99/0.97  --bmc1_max_bound_default                -1
% 1.99/0.97  --bmc1_symbol_reachability              true
% 1.99/0.97  --bmc1_property_lemmas                  false
% 1.99/0.97  --bmc1_k_induction                      false
% 1.99/0.97  --bmc1_non_equiv_states                 false
% 1.99/0.97  --bmc1_deadlock                         false
% 1.99/0.97  --bmc1_ucm                              false
% 1.99/0.97  --bmc1_add_unsat_core                   none
% 1.99/0.97  --bmc1_unsat_core_children              false
% 1.99/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.97  --bmc1_out_stat                         full
% 1.99/0.97  --bmc1_ground_init                      false
% 1.99/0.97  --bmc1_pre_inst_next_state              false
% 1.99/0.97  --bmc1_pre_inst_state                   false
% 1.99/0.97  --bmc1_pre_inst_reach_state             false
% 1.99/0.97  --bmc1_out_unsat_core                   false
% 1.99/0.97  --bmc1_aig_witness_out                  false
% 1.99/0.97  --bmc1_verbose                          false
% 1.99/0.97  --bmc1_dump_clauses_tptp                false
% 1.99/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.97  --bmc1_dump_file                        -
% 1.99/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.97  --bmc1_ucm_extend_mode                  1
% 1.99/0.97  --bmc1_ucm_init_mode                    2
% 1.99/0.97  --bmc1_ucm_cone_mode                    none
% 1.99/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.97  --bmc1_ucm_relax_model                  4
% 1.99/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.97  --bmc1_ucm_layered_model                none
% 1.99/0.97  --bmc1_ucm_max_lemma_size               10
% 1.99/0.97  
% 1.99/0.97  ------ AIG Options
% 1.99/0.97  
% 1.99/0.97  --aig_mode                              false
% 1.99/0.97  
% 1.99/0.97  ------ Instantiation Options
% 1.99/0.97  
% 1.99/0.97  --instantiation_flag                    true
% 1.99/0.97  --inst_sos_flag                         false
% 1.99/0.97  --inst_sos_phase                        true
% 1.99/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.97  --inst_lit_sel_side                     num_symb
% 1.99/0.97  --inst_solver_per_active                1400
% 1.99/0.97  --inst_solver_calls_frac                1.
% 1.99/0.97  --inst_passive_queue_type               priority_queues
% 1.99/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.97  --inst_passive_queues_freq              [25;2]
% 1.99/0.97  --inst_dismatching                      true
% 1.99/0.97  --inst_eager_unprocessed_to_passive     true
% 1.99/0.97  --inst_prop_sim_given                   true
% 1.99/0.97  --inst_prop_sim_new                     false
% 1.99/0.97  --inst_subs_new                         false
% 1.99/0.97  --inst_eq_res_simp                      false
% 1.99/0.97  --inst_subs_given                       false
% 1.99/0.97  --inst_orphan_elimination               true
% 1.99/0.97  --inst_learning_loop_flag               true
% 1.99/0.97  --inst_learning_start                   3000
% 1.99/0.97  --inst_learning_factor                  2
% 1.99/0.97  --inst_start_prop_sim_after_learn       3
% 1.99/0.97  --inst_sel_renew                        solver
% 1.99/0.97  --inst_lit_activity_flag                true
% 1.99/0.97  --inst_restr_to_given                   false
% 1.99/0.97  --inst_activity_threshold               500
% 1.99/0.97  --inst_out_proof                        true
% 1.99/0.97  
% 1.99/0.97  ------ Resolution Options
% 1.99/0.97  
% 1.99/0.97  --resolution_flag                       true
% 1.99/0.97  --res_lit_sel                           adaptive
% 1.99/0.97  --res_lit_sel_side                      none
% 1.99/0.97  --res_ordering                          kbo
% 1.99/0.97  --res_to_prop_solver                    active
% 1.99/0.97  --res_prop_simpl_new                    false
% 1.99/0.97  --res_prop_simpl_given                  true
% 1.99/0.97  --res_passive_queue_type                priority_queues
% 1.99/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.97  --res_passive_queues_freq               [15;5]
% 1.99/0.97  --res_forward_subs                      full
% 1.99/0.97  --res_backward_subs                     full
% 1.99/0.97  --res_forward_subs_resolution           true
% 1.99/0.97  --res_backward_subs_resolution          true
% 1.99/0.97  --res_orphan_elimination                true
% 1.99/0.97  --res_time_limit                        2.
% 1.99/0.97  --res_out_proof                         true
% 1.99/0.97  
% 1.99/0.97  ------ Superposition Options
% 1.99/0.97  
% 1.99/0.97  --superposition_flag                    true
% 1.99/0.97  --sup_passive_queue_type                priority_queues
% 1.99/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.97  --demod_completeness_check              fast
% 1.99/0.97  --demod_use_ground                      true
% 1.99/0.97  --sup_to_prop_solver                    passive
% 1.99/0.97  --sup_prop_simpl_new                    true
% 1.99/0.97  --sup_prop_simpl_given                  true
% 1.99/0.97  --sup_fun_splitting                     false
% 1.99/0.97  --sup_smt_interval                      50000
% 1.99/0.97  
% 1.99/0.97  ------ Superposition Simplification Setup
% 1.99/0.97  
% 1.99/0.97  --sup_indices_passive                   []
% 1.99/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_full_bw                           [BwDemod]
% 1.99/0.97  --sup_immed_triv                        [TrivRules]
% 1.99/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_immed_bw_main                     []
% 1.99/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.97  
% 1.99/0.97  ------ Combination Options
% 1.99/0.97  
% 1.99/0.97  --comb_res_mult                         3
% 1.99/0.97  --comb_sup_mult                         2
% 1.99/0.97  --comb_inst_mult                        10
% 1.99/0.97  
% 1.99/0.97  ------ Debug Options
% 1.99/0.97  
% 1.99/0.97  --dbg_backtrace                         false
% 1.99/0.97  --dbg_dump_prop_clauses                 false
% 1.99/0.97  --dbg_dump_prop_clauses_file            -
% 1.99/0.97  --dbg_out_stat                          false
% 1.99/0.97  ------ Parsing...
% 1.99/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.97  ------ Proving...
% 1.99/0.97  ------ Problem Properties 
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  clauses                                 16
% 1.99/0.97  conjectures                             1
% 1.99/0.97  EPR                                     2
% 1.99/0.97  Horn                                    16
% 1.99/0.97  unary                                   2
% 1.99/0.97  binary                                  9
% 1.99/0.97  lits                                    35
% 1.99/0.97  lits eq                                 20
% 1.99/0.97  fd_pure                                 0
% 1.99/0.97  fd_pseudo                               0
% 1.99/0.97  fd_cond                                 0
% 1.99/0.97  fd_pseudo_cond                          1
% 1.99/0.97  AC symbols                              0
% 1.99/0.97  
% 1.99/0.97  ------ Schedule dynamic 5 is on 
% 1.99/0.97  
% 1.99/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  ------ 
% 1.99/0.97  Current options:
% 1.99/0.97  ------ 
% 1.99/0.97  
% 1.99/0.97  ------ Input Options
% 1.99/0.97  
% 1.99/0.97  --out_options                           all
% 1.99/0.97  --tptp_safe_out                         true
% 1.99/0.97  --problem_path                          ""
% 1.99/0.97  --include_path                          ""
% 1.99/0.97  --clausifier                            res/vclausify_rel
% 1.99/0.97  --clausifier_options                    --mode clausify
% 1.99/0.97  --stdin                                 false
% 1.99/0.97  --stats_out                             all
% 1.99/0.97  
% 1.99/0.97  ------ General Options
% 1.99/0.97  
% 1.99/0.97  --fof                                   false
% 1.99/0.97  --time_out_real                         305.
% 1.99/0.97  --time_out_virtual                      -1.
% 1.99/0.97  --symbol_type_check                     false
% 1.99/0.97  --clausify_out                          false
% 1.99/0.97  --sig_cnt_out                           false
% 1.99/0.97  --trig_cnt_out                          false
% 1.99/0.97  --trig_cnt_out_tolerance                1.
% 1.99/0.97  --trig_cnt_out_sk_spl                   false
% 1.99/0.97  --abstr_cl_out                          false
% 1.99/0.97  
% 1.99/0.97  ------ Global Options
% 1.99/0.97  
% 1.99/0.97  --schedule                              default
% 1.99/0.97  --add_important_lit                     false
% 1.99/0.97  --prop_solver_per_cl                    1000
% 1.99/0.97  --min_unsat_core                        false
% 1.99/0.97  --soft_assumptions                      false
% 1.99/0.97  --soft_lemma_size                       3
% 1.99/0.97  --prop_impl_unit_size                   0
% 1.99/0.97  --prop_impl_unit                        []
% 1.99/0.97  --share_sel_clauses                     true
% 1.99/0.97  --reset_solvers                         false
% 1.99/0.97  --bc_imp_inh                            [conj_cone]
% 1.99/0.97  --conj_cone_tolerance                   3.
% 1.99/0.97  --extra_neg_conj                        none
% 1.99/0.97  --large_theory_mode                     true
% 1.99/0.97  --prolific_symb_bound                   200
% 1.99/0.97  --lt_threshold                          2000
% 1.99/0.97  --clause_weak_htbl                      true
% 1.99/0.97  --gc_record_bc_elim                     false
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing Options
% 1.99/0.97  
% 1.99/0.97  --preprocessing_flag                    true
% 1.99/0.97  --time_out_prep_mult                    0.1
% 1.99/0.97  --splitting_mode                        input
% 1.99/0.97  --splitting_grd                         true
% 1.99/0.97  --splitting_cvd                         false
% 1.99/0.97  --splitting_cvd_svl                     false
% 1.99/0.97  --splitting_nvd                         32
% 1.99/0.97  --sub_typing                            true
% 1.99/0.97  --prep_gs_sim                           true
% 1.99/0.97  --prep_unflatten                        true
% 1.99/0.97  --prep_res_sim                          true
% 1.99/0.97  --prep_upred                            true
% 1.99/0.97  --prep_sem_filter                       exhaustive
% 1.99/0.97  --prep_sem_filter_out                   false
% 1.99/0.97  --pred_elim                             true
% 1.99/0.97  --res_sim_input                         true
% 1.99/0.97  --eq_ax_congr_red                       true
% 1.99/0.97  --pure_diseq_elim                       true
% 1.99/0.97  --brand_transform                       false
% 1.99/0.97  --non_eq_to_eq                          false
% 1.99/0.97  --prep_def_merge                        true
% 1.99/0.97  --prep_def_merge_prop_impl              false
% 1.99/0.97  --prep_def_merge_mbd                    true
% 1.99/0.97  --prep_def_merge_tr_red                 false
% 1.99/0.97  --prep_def_merge_tr_cl                  false
% 1.99/0.97  --smt_preprocessing                     true
% 1.99/0.97  --smt_ac_axioms                         fast
% 1.99/0.97  --preprocessed_out                      false
% 1.99/0.97  --preprocessed_stats                    false
% 1.99/0.97  
% 1.99/0.97  ------ Abstraction refinement Options
% 1.99/0.97  
% 1.99/0.97  --abstr_ref                             []
% 1.99/0.97  --abstr_ref_prep                        false
% 1.99/0.97  --abstr_ref_until_sat                   false
% 1.99/0.97  --abstr_ref_sig_restrict                funpre
% 1.99/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.97  --abstr_ref_under                       []
% 1.99/0.97  
% 1.99/0.97  ------ SAT Options
% 1.99/0.97  
% 1.99/0.97  --sat_mode                              false
% 1.99/0.97  --sat_fm_restart_options                ""
% 1.99/0.97  --sat_gr_def                            false
% 1.99/0.97  --sat_epr_types                         true
% 1.99/0.97  --sat_non_cyclic_types                  false
% 1.99/0.97  --sat_finite_models                     false
% 1.99/0.97  --sat_fm_lemmas                         false
% 1.99/0.97  --sat_fm_prep                           false
% 1.99/0.97  --sat_fm_uc_incr                        true
% 1.99/0.97  --sat_out_model                         small
% 1.99/0.97  --sat_out_clauses                       false
% 1.99/0.97  
% 1.99/0.97  ------ QBF Options
% 1.99/0.97  
% 1.99/0.97  --qbf_mode                              false
% 1.99/0.97  --qbf_elim_univ                         false
% 1.99/0.97  --qbf_dom_inst                          none
% 1.99/0.97  --qbf_dom_pre_inst                      false
% 1.99/0.97  --qbf_sk_in                             false
% 1.99/0.97  --qbf_pred_elim                         true
% 1.99/0.97  --qbf_split                             512
% 1.99/0.97  
% 1.99/0.97  ------ BMC1 Options
% 1.99/0.97  
% 1.99/0.97  --bmc1_incremental                      false
% 1.99/0.97  --bmc1_axioms                           reachable_all
% 1.99/0.97  --bmc1_min_bound                        0
% 1.99/0.97  --bmc1_max_bound                        -1
% 1.99/0.97  --bmc1_max_bound_default                -1
% 1.99/0.97  --bmc1_symbol_reachability              true
% 1.99/0.97  --bmc1_property_lemmas                  false
% 1.99/0.97  --bmc1_k_induction                      false
% 1.99/0.97  --bmc1_non_equiv_states                 false
% 1.99/0.97  --bmc1_deadlock                         false
% 1.99/0.97  --bmc1_ucm                              false
% 1.99/0.97  --bmc1_add_unsat_core                   none
% 1.99/0.97  --bmc1_unsat_core_children              false
% 1.99/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.97  --bmc1_out_stat                         full
% 1.99/0.97  --bmc1_ground_init                      false
% 1.99/0.97  --bmc1_pre_inst_next_state              false
% 1.99/0.97  --bmc1_pre_inst_state                   false
% 1.99/0.97  --bmc1_pre_inst_reach_state             false
% 1.99/0.97  --bmc1_out_unsat_core                   false
% 1.99/0.97  --bmc1_aig_witness_out                  false
% 1.99/0.97  --bmc1_verbose                          false
% 1.99/0.97  --bmc1_dump_clauses_tptp                false
% 1.99/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.97  --bmc1_dump_file                        -
% 1.99/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.97  --bmc1_ucm_extend_mode                  1
% 1.99/0.97  --bmc1_ucm_init_mode                    2
% 1.99/0.97  --bmc1_ucm_cone_mode                    none
% 1.99/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.97  --bmc1_ucm_relax_model                  4
% 1.99/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.97  --bmc1_ucm_layered_model                none
% 1.99/0.97  --bmc1_ucm_max_lemma_size               10
% 1.99/0.97  
% 1.99/0.97  ------ AIG Options
% 1.99/0.97  
% 1.99/0.97  --aig_mode                              false
% 1.99/0.97  
% 1.99/0.97  ------ Instantiation Options
% 1.99/0.97  
% 1.99/0.97  --instantiation_flag                    true
% 1.99/0.97  --inst_sos_flag                         false
% 1.99/0.97  --inst_sos_phase                        true
% 1.99/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.97  --inst_lit_sel_side                     none
% 1.99/0.97  --inst_solver_per_active                1400
% 1.99/0.97  --inst_solver_calls_frac                1.
% 1.99/0.97  --inst_passive_queue_type               priority_queues
% 1.99/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.97  --inst_passive_queues_freq              [25;2]
% 1.99/0.97  --inst_dismatching                      true
% 1.99/0.97  --inst_eager_unprocessed_to_passive     true
% 1.99/0.97  --inst_prop_sim_given                   true
% 1.99/0.97  --inst_prop_sim_new                     false
% 1.99/0.97  --inst_subs_new                         false
% 1.99/0.97  --inst_eq_res_simp                      false
% 1.99/0.97  --inst_subs_given                       false
% 1.99/0.97  --inst_orphan_elimination               true
% 1.99/0.97  --inst_learning_loop_flag               true
% 1.99/0.97  --inst_learning_start                   3000
% 1.99/0.97  --inst_learning_factor                  2
% 1.99/0.97  --inst_start_prop_sim_after_learn       3
% 1.99/0.97  --inst_sel_renew                        solver
% 1.99/0.97  --inst_lit_activity_flag                true
% 1.99/0.97  --inst_restr_to_given                   false
% 1.99/0.97  --inst_activity_threshold               500
% 1.99/0.97  --inst_out_proof                        true
% 1.99/0.97  
% 1.99/0.97  ------ Resolution Options
% 1.99/0.97  
% 1.99/0.97  --resolution_flag                       false
% 1.99/0.97  --res_lit_sel                           adaptive
% 1.99/0.97  --res_lit_sel_side                      none
% 1.99/0.97  --res_ordering                          kbo
% 1.99/0.97  --res_to_prop_solver                    active
% 1.99/0.97  --res_prop_simpl_new                    false
% 1.99/0.97  --res_prop_simpl_given                  true
% 1.99/0.97  --res_passive_queue_type                priority_queues
% 1.99/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.97  --res_passive_queues_freq               [15;5]
% 1.99/0.97  --res_forward_subs                      full
% 1.99/0.97  --res_backward_subs                     full
% 1.99/0.97  --res_forward_subs_resolution           true
% 1.99/0.97  --res_backward_subs_resolution          true
% 1.99/0.97  --res_orphan_elimination                true
% 1.99/0.97  --res_time_limit                        2.
% 1.99/0.97  --res_out_proof                         true
% 1.99/0.97  
% 1.99/0.97  ------ Superposition Options
% 1.99/0.97  
% 1.99/0.97  --superposition_flag                    true
% 1.99/0.97  --sup_passive_queue_type                priority_queues
% 1.99/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.97  --demod_completeness_check              fast
% 1.99/0.97  --demod_use_ground                      true
% 1.99/0.97  --sup_to_prop_solver                    passive
% 1.99/0.97  --sup_prop_simpl_new                    true
% 1.99/0.97  --sup_prop_simpl_given                  true
% 1.99/0.97  --sup_fun_splitting                     false
% 1.99/0.97  --sup_smt_interval                      50000
% 1.99/0.97  
% 1.99/0.97  ------ Superposition Simplification Setup
% 1.99/0.97  
% 1.99/0.97  --sup_indices_passive                   []
% 1.99/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_full_bw                           [BwDemod]
% 1.99/0.97  --sup_immed_triv                        [TrivRules]
% 1.99/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_immed_bw_main                     []
% 1.99/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.97  
% 1.99/0.97  ------ Combination Options
% 1.99/0.97  
% 1.99/0.97  --comb_res_mult                         3
% 1.99/0.97  --comb_sup_mult                         2
% 1.99/0.97  --comb_inst_mult                        10
% 1.99/0.97  
% 1.99/0.97  ------ Debug Options
% 1.99/0.97  
% 1.99/0.97  --dbg_backtrace                         false
% 1.99/0.97  --dbg_dump_prop_clauses                 false
% 1.99/0.97  --dbg_dump_prop_clauses_file            -
% 1.99/0.97  --dbg_out_stat                          false
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  ------ Proving...
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  % SZS status Theorem for theBenchmark.p
% 1.99/0.97  
% 1.99/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/0.97  
% 1.99/0.97  fof(f3,axiom,(
% 1.99/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f19,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.99/0.97    inference(ennf_transformation,[],[f3])).
% 1.99/0.97  
% 1.99/0.97  fof(f43,plain,(
% 1.99/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f19])).
% 1.99/0.97  
% 1.99/0.97  fof(f16,conjecture,(
% 1.99/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f17,negated_conjecture,(
% 1.99/0.97    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 1.99/0.97    inference(negated_conjecture,[],[f16])).
% 1.99/0.97  
% 1.99/0.97  fof(f33,plain,(
% 1.99/0.97    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.99/0.97    inference(ennf_transformation,[],[f17])).
% 1.99/0.97  
% 1.99/0.97  fof(f37,plain,(
% 1.99/0.97    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f38,plain,(
% 1.99/0.97    (k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.99/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f58,plain,(
% 1.99/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.99/0.97    inference(cnf_transformation,[],[f38])).
% 1.99/0.97  
% 1.99/0.97  fof(f5,axiom,(
% 1.99/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f46,plain,(
% 1.99/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.99/0.97    inference(cnf_transformation,[],[f5])).
% 1.99/0.97  
% 1.99/0.97  fof(f1,axiom,(
% 1.99/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f34,plain,(
% 1.99/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/0.97    inference(nnf_transformation,[],[f1])).
% 1.99/0.97  
% 1.99/0.97  fof(f35,plain,(
% 1.99/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/0.97    inference(flattening,[],[f34])).
% 1.99/0.97  
% 1.99/0.97  fof(f40,plain,(
% 1.99/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.99/0.97    inference(cnf_transformation,[],[f35])).
% 1.99/0.97  
% 1.99/0.97  fof(f60,plain,(
% 1.99/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.99/0.97    inference(equality_resolution,[],[f40])).
% 1.99/0.97  
% 1.99/0.97  fof(f10,axiom,(
% 1.99/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f26,plain,(
% 1.99/0.97    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/0.97    inference(ennf_transformation,[],[f10])).
% 1.99/0.97  
% 1.99/0.97  fof(f27,plain,(
% 1.99/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.99/0.97    inference(flattening,[],[f26])).
% 1.99/0.97  
% 1.99/0.97  fof(f51,plain,(
% 1.99/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f27])).
% 1.99/0.97  
% 1.99/0.97  fof(f6,axiom,(
% 1.99/0.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f21,plain,(
% 1.99/0.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.99/0.97    inference(ennf_transformation,[],[f6])).
% 1.99/0.97  
% 1.99/0.97  fof(f47,plain,(
% 1.99/0.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f21])).
% 1.99/0.97  
% 1.99/0.97  fof(f11,axiom,(
% 1.99/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f28,plain,(
% 1.99/0.97    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.97    inference(ennf_transformation,[],[f11])).
% 1.99/0.97  
% 1.99/0.97  fof(f52,plain,(
% 1.99/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.97    inference(cnf_transformation,[],[f28])).
% 1.99/0.97  
% 1.99/0.97  fof(f9,axiom,(
% 1.99/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f24,plain,(
% 1.99/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.99/0.97    inference(ennf_transformation,[],[f9])).
% 1.99/0.97  
% 1.99/0.97  fof(f25,plain,(
% 1.99/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.99/0.97    inference(flattening,[],[f24])).
% 1.99/0.97  
% 1.99/0.97  fof(f50,plain,(
% 1.99/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f25])).
% 1.99/0.97  
% 1.99/0.97  fof(f12,axiom,(
% 1.99/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f29,plain,(
% 1.99/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.97    inference(ennf_transformation,[],[f12])).
% 1.99/0.97  
% 1.99/0.97  fof(f54,plain,(
% 1.99/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.97    inference(cnf_transformation,[],[f29])).
% 1.99/0.97  
% 1.99/0.97  fof(f13,axiom,(
% 1.99/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f30,plain,(
% 1.99/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.97    inference(ennf_transformation,[],[f13])).
% 1.99/0.97  
% 1.99/0.97  fof(f55,plain,(
% 1.99/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.97    inference(cnf_transformation,[],[f30])).
% 1.99/0.97  
% 1.99/0.97  fof(f59,plain,(
% 1.99/0.97    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 1.99/0.97    inference(cnf_transformation,[],[f38])).
% 1.99/0.97  
% 1.99/0.97  fof(f15,axiom,(
% 1.99/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f32,plain,(
% 1.99/0.97    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.97    inference(ennf_transformation,[],[f15])).
% 1.99/0.97  
% 1.99/0.97  fof(f57,plain,(
% 1.99/0.97    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.97    inference(cnf_transformation,[],[f32])).
% 1.99/0.97  
% 1.99/0.97  fof(f14,axiom,(
% 1.99/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f31,plain,(
% 1.99/0.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.97    inference(ennf_transformation,[],[f14])).
% 1.99/0.97  
% 1.99/0.97  fof(f56,plain,(
% 1.99/0.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.97    inference(cnf_transformation,[],[f31])).
% 1.99/0.97  
% 1.99/0.97  fof(f8,axiom,(
% 1.99/0.97    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f23,plain,(
% 1.99/0.97    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.99/0.97    inference(ennf_transformation,[],[f8])).
% 1.99/0.97  
% 1.99/0.97  fof(f49,plain,(
% 1.99/0.97    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f23])).
% 1.99/0.97  
% 1.99/0.97  fof(f53,plain,(
% 1.99/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.97    inference(cnf_transformation,[],[f28])).
% 1.99/0.97  
% 1.99/0.97  fof(f4,axiom,(
% 1.99/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f20,plain,(
% 1.99/0.97    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/0.97    inference(ennf_transformation,[],[f4])).
% 1.99/0.97  
% 1.99/0.97  fof(f36,plain,(
% 1.99/0.97    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.99/0.97    inference(nnf_transformation,[],[f20])).
% 1.99/0.97  
% 1.99/0.97  fof(f44,plain,(
% 1.99/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f36])).
% 1.99/0.97  
% 1.99/0.97  fof(f2,axiom,(
% 1.99/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f18,plain,(
% 1.99/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.99/0.97    inference(ennf_transformation,[],[f2])).
% 1.99/0.97  
% 1.99/0.97  fof(f42,plain,(
% 1.99/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f18])).
% 1.99/0.97  
% 1.99/0.97  fof(f7,axiom,(
% 1.99/0.97    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f22,plain,(
% 1.99/0.97    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/0.97    inference(ennf_transformation,[],[f7])).
% 1.99/0.97  
% 1.99/0.97  fof(f48,plain,(
% 1.99/0.97    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f22])).
% 1.99/0.97  
% 1.99/0.97  cnf(c_4,plain,
% 1.99/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.97      | ~ v1_relat_1(X1)
% 1.99/0.97      | v1_relat_1(X0) ),
% 1.99/0.97      inference(cnf_transformation,[],[f43]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_20,negated_conjecture,
% 1.99/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.99/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_273,plain,
% 1.99/0.97      ( ~ v1_relat_1(X0)
% 1.99/0.97      | v1_relat_1(X1)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 1.99/0.97      | sK2 != X1 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_274,plain,
% 1.99/0.97      ( ~ v1_relat_1(X0)
% 1.99/0.97      | v1_relat_1(sK2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_273]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_684,plain,
% 1.99/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 1.99/0.97      | v1_relat_1(X0) != iProver_top
% 1.99/0.97      | v1_relat_1(sK2) = iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_462,plain,( X0 = X0 ),theory(equality) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_792,plain,
% 1.99/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_462]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_787,plain,
% 1.99/0.97      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 1.99/0.97      | v1_relat_1(sK2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_274]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_893,plain,
% 1.99/0.97      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | v1_relat_1(sK2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_787]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_894,plain,
% 1.99/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 1.99/0.97      | v1_relat_1(sK2) = iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_893]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_7,plain,
% 1.99/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/0.97      inference(cnf_transformation,[],[f46]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_985,plain,
% 1.99/0.97      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_986,plain,
% 1.99/0.97      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1210,plain,
% 1.99/0.97      ( v1_relat_1(sK2) = iProver_top ),
% 1.99/0.97      inference(global_propositional_subsumption,
% 1.99/0.97                [status(thm)],
% 1.99/0.97                [c_684,c_792,c_894,c_986]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1,plain,
% 1.99/0.97      ( r1_tarski(X0,X0) ),
% 1.99/0.97      inference(cnf_transformation,[],[f60]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_691,plain,
% 1.99/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_12,plain,
% 1.99/0.97      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 1.99/0.97      | ~ v1_relat_1(X0)
% 1.99/0.97      | k7_relat_1(X0,X1) = X0 ),
% 1.99/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_685,plain,
% 1.99/0.97      ( k7_relat_1(X0,X1) = X0
% 1.99/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 1.99/0.97      | v1_relat_1(X0) != iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1601,plain,
% 1.99/0.97      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 1.99/0.97      | v1_relat_1(X0) != iProver_top ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_691,c_685]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1957,plain,
% 1.99/0.97      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_1210,c_1601]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_8,plain,
% 1.99/0.97      ( ~ v1_relat_1(X0)
% 1.99/0.97      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 1.99/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_688,plain,
% 1.99/0.97      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 1.99/0.97      | v1_relat_1(X0) != iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1512,plain,
% 1.99/0.97      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_1210,c_688]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2286,plain,
% 1.99/0.97      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_1957,c_1512]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_14,plain,
% 1.99/0.97      ( v4_relat_1(X0,X1)
% 1.99/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.99/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_11,plain,
% 1.99/0.97      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.99/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_236,plain,
% 1.99/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.97      | ~ v1_relat_1(X0)
% 1.99/0.97      | k7_relat_1(X0,X1) = X0 ),
% 1.99/0.97      inference(resolution,[status(thm)],[c_14,c_11]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_303,plain,
% 1.99/0.97      ( ~ v1_relat_1(X0)
% 1.99/0.97      | k7_relat_1(X0,X1) = X0
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | sK2 != X0 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_236,c_20]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_304,plain,
% 1.99/0.97      ( ~ v1_relat_1(sK2)
% 1.99/0.97      | k7_relat_1(sK2,X0) = sK2
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_303]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_682,plain,
% 1.99/0.97      ( k7_relat_1(sK2,X0) = sK2
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | v1_relat_1(sK2) != iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_967,plain,
% 1.99/0.97      ( k7_relat_1(sK2,sK1) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 1.99/0.97      inference(equality_resolution,[status(thm)],[c_682]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_968,plain,
% 1.99/0.97      ( ~ v1_relat_1(sK2) | k7_relat_1(sK2,sK1) = sK2 ),
% 1.99/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_967]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1454,plain,
% 1.99/0.97      ( k7_relat_1(sK2,sK1) = sK2 ),
% 1.99/0.97      inference(global_propositional_subsumption,
% 1.99/0.97                [status(thm)],
% 1.99/0.97                [c_967,c_792,c_893,c_968,c_985]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1684,plain,
% 1.99/0.97      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_1454,c_1512]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_15,plain,
% 1.99/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.99/0.97      inference(cnf_transformation,[],[f54]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_345,plain,
% 1.99/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | sK2 != X2 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_346,plain,
% 1.99/0.97      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_345]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_840,plain,
% 1.99/0.97      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 1.99/0.97      inference(equality_resolution,[status(thm)],[c_346]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_16,plain,
% 1.99/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.99/0.97      inference(cnf_transformation,[],[f55]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_336,plain,
% 1.99/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | sK2 != X2 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_337,plain,
% 1.99/0.97      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_336]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_803,plain,
% 1.99/0.97      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 1.99/0.97      inference(equality_resolution,[status(thm)],[c_337]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_19,negated_conjecture,
% 1.99/0.97      ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
% 1.99/0.97      | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
% 1.99/0.97      inference(cnf_transformation,[],[f59]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_855,plain,
% 1.99/0.97      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 1.99/0.97      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 1.99/0.97      inference(demodulation,[status(thm)],[c_803,c_19]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_881,plain,
% 1.99/0.97      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
% 1.99/0.97      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 1.99/0.97      inference(demodulation,[status(thm)],[c_840,c_855]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_18,plain,
% 1.99/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.97      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.99/0.97      inference(cnf_transformation,[],[f57]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_318,plain,
% 1.99/0.97      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | sK2 != X2 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_319,plain,
% 1.99/0.97      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_318]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_843,plain,
% 1.99/0.97      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 1.99/0.97      inference(equality_resolution,[status(thm)],[c_319]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_17,plain,
% 1.99/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.97      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.99/0.97      inference(cnf_transformation,[],[f56]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_327,plain,
% 1.99/0.97      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | sK2 != X2 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_328,plain,
% 1.99/0.97      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_327]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_852,plain,
% 1.99/0.97      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 1.99/0.97      inference(equality_resolution,[status(thm)],[c_328]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1320,plain,
% 1.99/0.97      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
% 1.99/0.97      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 1.99/0.97      inference(demodulation,[status(thm)],[c_881,c_843,c_852]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1746,plain,
% 1.99/0.97      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 1.99/0.97      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 1.99/0.97      inference(demodulation,[status(thm)],[c_1684,c_1320]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_10,plain,
% 1.99/0.97      ( ~ v1_relat_1(X0)
% 1.99/0.97      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 1.99/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_686,plain,
% 1.99/0.97      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 1.99/0.97      | v1_relat_1(X0) != iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1215,plain,
% 1.99/0.97      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_1210,c_686]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1747,plain,
% 1.99/0.97      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 1.99/0.97      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 1.99/0.97      inference(light_normalisation,[status(thm)],[c_1746,c_1215]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1748,plain,
% 1.99/0.97      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 1.99/0.97      inference(equality_resolution_simp,[status(thm)],[c_1747]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_13,plain,
% 1.99/0.97      ( v5_relat_1(X0,X1)
% 1.99/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.99/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_6,plain,
% 1.99/0.97      ( ~ v5_relat_1(X0,X1)
% 1.99/0.97      | r1_tarski(k2_relat_1(X0),X1)
% 1.99/0.97      | ~ v1_relat_1(X0) ),
% 1.99/0.97      inference(cnf_transformation,[],[f44]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_254,plain,
% 1.99/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.97      | r1_tarski(k2_relat_1(X0),X2)
% 1.99/0.97      | ~ v1_relat_1(X0) ),
% 1.99/0.97      inference(resolution,[status(thm)],[c_13,c_6]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_288,plain,
% 1.99/0.97      ( r1_tarski(k2_relat_1(X0),X1)
% 1.99/0.97      | ~ v1_relat_1(X0)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | sK2 != X0 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_254,c_20]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_289,plain,
% 1.99/0.97      ( r1_tarski(k2_relat_1(sK2),X0)
% 1.99/0.97      | ~ v1_relat_1(sK2)
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_288]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_683,plain,
% 1.99/0.97      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 1.99/0.97      | v1_relat_1(sK2) != iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_290,plain,
% 1.99/0.97      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 1.99/0.97      | v1_relat_1(sK2) != iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1310,plain,
% 1.99/0.97      ( r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 1.99/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.99/0.97      inference(global_propositional_subsumption,
% 1.99/0.97                [status(thm)],
% 1.99/0.97                [c_683,c_290,c_792,c_894,c_986]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1311,plain,
% 1.99/0.97      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.99/0.97      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
% 1.99/0.97      inference(renaming,[status(thm)],[c_1310]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1318,plain,
% 1.99/0.97      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 1.99/0.97      inference(equality_resolution,[status(thm)],[c_1311]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3,plain,
% 1.99/0.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.99/0.97      inference(cnf_transformation,[],[f42]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_690,plain,
% 1.99/0.97      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1386,plain,
% 1.99/0.97      ( k3_xboole_0(k2_relat_1(sK2),sK0) = k2_relat_1(sK2) ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_1318,c_690]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_9,plain,
% 1.99/0.97      ( ~ v1_relat_1(X0)
% 1.99/0.97      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 1.99/0.97      inference(cnf_transformation,[],[f48]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_687,plain,
% 1.99/0.97      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 1.99/0.97      | v1_relat_1(X0) != iProver_top ),
% 1.99/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1523,plain,
% 1.99/0.97      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_1210,c_687]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1750,plain,
% 1.99/0.97      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK0) ),
% 1.99/0.97      inference(superposition,[status(thm)],[c_1386,c_1523]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1751,plain,
% 1.99/0.97      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 1.99/0.97      inference(light_normalisation,[status(thm)],[c_1750,c_1215]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1867,plain,
% 1.99/0.97      ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 1.99/0.97      inference(light_normalisation,[status(thm)],[c_1748,c_1751]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(contradiction,plain,
% 1.99/0.97      ( $false ),
% 1.99/0.97      inference(minisat,[status(thm)],[c_2286,c_1867]) ).
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/0.97  
% 1.99/0.97  ------                               Statistics
% 1.99/0.97  
% 1.99/0.97  ------ General
% 1.99/0.97  
% 1.99/0.97  abstr_ref_over_cycles:                  0
% 1.99/0.97  abstr_ref_under_cycles:                 0
% 1.99/0.97  gc_basic_clause_elim:                   0
% 1.99/0.97  forced_gc_time:                         0
% 1.99/0.97  parsing_time:                           0.008
% 1.99/0.97  unif_index_cands_time:                  0.
% 1.99/0.97  unif_index_add_time:                    0.
% 1.99/0.97  orderings_time:                         0.
% 1.99/0.97  out_proof_time:                         0.011
% 1.99/0.97  total_time:                             0.104
% 1.99/0.97  num_of_symbols:                         51
% 1.99/0.97  num_of_terms:                           1838
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing
% 1.99/0.97  
% 1.99/0.97  num_of_splits:                          0
% 1.99/0.97  num_of_split_atoms:                     0
% 1.99/0.97  num_of_reused_defs:                     0
% 1.99/0.97  num_eq_ax_congr_red:                    20
% 1.99/0.97  num_of_sem_filtered_clauses:            1
% 1.99/0.97  num_of_subtypes:                        0
% 1.99/0.97  monotx_restored_types:                  0
% 1.99/0.97  sat_num_of_epr_types:                   0
% 1.99/0.97  sat_num_of_non_cyclic_types:            0
% 1.99/0.97  sat_guarded_non_collapsed_types:        0
% 1.99/0.97  num_pure_diseq_elim:                    0
% 1.99/0.97  simp_replaced_by:                       0
% 1.99/0.97  res_preprocessed:                       101
% 1.99/0.97  prep_upred:                             0
% 1.99/0.97  prep_unflattend:                        7
% 1.99/0.97  smt_new_axioms:                         0
% 1.99/0.97  pred_elim_cands:                        2
% 1.99/0.97  pred_elim:                              3
% 1.99/0.97  pred_elim_cl:                           4
% 1.99/0.97  pred_elim_cycles:                       5
% 1.99/0.97  merged_defs:                            0
% 1.99/0.97  merged_defs_ncl:                        0
% 1.99/0.97  bin_hyper_res:                          0
% 1.99/0.97  prep_cycles:                            4
% 1.99/0.97  pred_elim_time:                         0.003
% 1.99/0.97  splitting_time:                         0.
% 1.99/0.97  sem_filter_time:                        0.
% 1.99/0.97  monotx_time:                            0.
% 1.99/0.97  subtype_inf_time:                       0.
% 1.99/0.97  
% 1.99/0.97  ------ Problem properties
% 1.99/0.97  
% 1.99/0.97  clauses:                                16
% 1.99/0.97  conjectures:                            1
% 1.99/0.97  epr:                                    2
% 1.99/0.97  horn:                                   16
% 1.99/0.97  ground:                                 1
% 1.99/0.97  unary:                                  2
% 1.99/0.97  binary:                                 9
% 1.99/0.97  lits:                                   35
% 1.99/0.97  lits_eq:                                20
% 1.99/0.97  fd_pure:                                0
% 1.99/0.97  fd_pseudo:                              0
% 1.99/0.97  fd_cond:                                0
% 1.99/0.97  fd_pseudo_cond:                         1
% 1.99/0.97  ac_symbols:                             0
% 1.99/0.97  
% 1.99/0.97  ------ Propositional Solver
% 1.99/0.97  
% 1.99/0.97  prop_solver_calls:                      28
% 1.99/0.97  prop_fast_solver_calls:                 576
% 1.99/0.97  smt_solver_calls:                       0
% 1.99/0.97  smt_fast_solver_calls:                  0
% 1.99/0.97  prop_num_of_clauses:                    795
% 1.99/0.97  prop_preprocess_simplified:             3630
% 1.99/0.97  prop_fo_subsumed:                       4
% 1.99/0.97  prop_solver_time:                       0.
% 1.99/0.97  smt_solver_time:                        0.
% 1.99/0.97  smt_fast_solver_time:                   0.
% 1.99/0.97  prop_fast_solver_time:                  0.
% 1.99/0.97  prop_unsat_core_time:                   0.
% 1.99/0.97  
% 1.99/0.97  ------ QBF
% 1.99/0.97  
% 1.99/0.97  qbf_q_res:                              0
% 1.99/0.97  qbf_num_tautologies:                    0
% 1.99/0.97  qbf_prep_cycles:                        0
% 1.99/0.97  
% 1.99/0.97  ------ BMC1
% 1.99/0.97  
% 1.99/0.97  bmc1_current_bound:                     -1
% 1.99/0.97  bmc1_last_solved_bound:                 -1
% 1.99/0.97  bmc1_unsat_core_size:                   -1
% 1.99/0.97  bmc1_unsat_core_parents_size:           -1
% 1.99/0.97  bmc1_merge_next_fun:                    0
% 1.99/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.99/0.97  
% 1.99/0.97  ------ Instantiation
% 1.99/0.97  
% 1.99/0.97  inst_num_of_clauses:                    284
% 1.99/0.97  inst_num_in_passive:                    85
% 1.99/0.97  inst_num_in_active:                     192
% 1.99/0.97  inst_num_in_unprocessed:                7
% 1.99/0.97  inst_num_of_loops:                      200
% 1.99/0.97  inst_num_of_learning_restarts:          0
% 1.99/0.97  inst_num_moves_active_passive:          5
% 1.99/0.97  inst_lit_activity:                      0
% 1.99/0.97  inst_lit_activity_moves:                0
% 1.99/0.97  inst_num_tautologies:                   0
% 1.99/0.97  inst_num_prop_implied:                  0
% 1.99/0.97  inst_num_existing_simplified:           0
% 1.99/0.97  inst_num_eq_res_simplified:             0
% 1.99/0.97  inst_num_child_elim:                    0
% 1.99/0.97  inst_num_of_dismatching_blockings:      66
% 1.99/0.97  inst_num_of_non_proper_insts:           350
% 1.99/0.97  inst_num_of_duplicates:                 0
% 1.99/0.97  inst_inst_num_from_inst_to_res:         0
% 1.99/0.97  inst_dismatching_checking_time:         0.
% 1.99/0.97  
% 1.99/0.97  ------ Resolution
% 1.99/0.97  
% 1.99/0.97  res_num_of_clauses:                     0
% 1.99/0.97  res_num_in_passive:                     0
% 1.99/0.97  res_num_in_active:                      0
% 1.99/0.97  res_num_of_loops:                       105
% 1.99/0.97  res_forward_subset_subsumed:            84
% 1.99/0.97  res_backward_subset_subsumed:           2
% 1.99/0.97  res_forward_subsumed:                   0
% 1.99/0.97  res_backward_subsumed:                  0
% 1.99/0.97  res_forward_subsumption_resolution:     0
% 1.99/0.97  res_backward_subsumption_resolution:    0
% 1.99/0.97  res_clause_to_clause_subsumption:       47
% 1.99/0.97  res_orphan_elimination:                 0
% 1.99/0.97  res_tautology_del:                      48
% 1.99/0.97  res_num_eq_res_simplified:              0
% 1.99/0.97  res_num_sel_changes:                    0
% 1.99/0.97  res_moves_from_active_to_pass:          0
% 1.99/0.97  
% 1.99/0.97  ------ Superposition
% 1.99/0.97  
% 1.99/0.97  sup_time_total:                         0.
% 1.99/0.97  sup_time_generating:                    0.
% 1.99/0.97  sup_time_sim_full:                      0.
% 1.99/0.97  sup_time_sim_immed:                     0.
% 1.99/0.97  
% 1.99/0.97  sup_num_of_clauses:                     38
% 1.99/0.97  sup_num_in_active:                      36
% 1.99/0.97  sup_num_in_passive:                     2
% 1.99/0.97  sup_num_of_loops:                       38
% 1.99/0.97  sup_fw_superposition:                   12
% 1.99/0.97  sup_bw_superposition:                   5
% 1.99/0.97  sup_immediate_simplified:               2
% 1.99/0.97  sup_given_eliminated:                   0
% 1.99/0.97  comparisons_done:                       0
% 1.99/0.97  comparisons_avoided:                    0
% 1.99/0.97  
% 1.99/0.97  ------ Simplifications
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  sim_fw_subset_subsumed:                 0
% 1.99/0.97  sim_bw_subset_subsumed:                 0
% 1.99/0.97  sim_fw_subsumed:                        0
% 1.99/0.97  sim_bw_subsumed:                        0
% 1.99/0.97  sim_fw_subsumption_res:                 0
% 1.99/0.97  sim_bw_subsumption_res:                 0
% 1.99/0.97  sim_tautology_del:                      0
% 1.99/0.97  sim_eq_tautology_del:                   1
% 1.99/0.97  sim_eq_res_simp:                        1
% 1.99/0.97  sim_fw_demodulated:                     1
% 1.99/0.97  sim_bw_demodulated:                     3
% 1.99/0.97  sim_light_normalised:                   3
% 1.99/0.97  sim_joinable_taut:                      0
% 1.99/0.97  sim_joinable_simp:                      0
% 1.99/0.97  sim_ac_normalised:                      0
% 1.99/0.97  sim_smt_subsumption:                    0
% 1.99/0.97  
%------------------------------------------------------------------------------
