%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:00 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 241 expanded)
%              Number of clauses        :   59 (  95 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  246 ( 573 expanded)
%              Number of equality atoms :  115 ( 276 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK1,sK2,sK3) != k8_relset_1(sK1,sK2,sK3,sK2)
        | k2_relset_1(sK1,sK2,sK3) != k7_relset_1(sK1,sK2,sK3,sK1) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( k1_relset_1(sK1,sK2,sK3) != k8_relset_1(sK1,sK2,sK3,sK2)
      | k2_relset_1(sK1,sK2,sK3) != k7_relset_1(sK1,sK2,sK3,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f45])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,
    ( k1_relset_1(sK1,sK2,sK3) != k8_relset_1(sK1,sK2,sK3,sK2)
    | k2_relset_1(sK1,sK2,sK3) != k7_relset_1(sK1,sK2,sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_20,c_17])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_20,c_18,c_17])).

cnf(c_2110,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_4398,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_2111,c_2110])).

cnf(c_2116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2408,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2111,c_2116])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2120,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2592,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2408,c_2120])).

cnf(c_4510,plain,
    ( k9_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4398,c_2592])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_12])).

cnf(c_400,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_18])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_400])).

cnf(c_2109,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_3766,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2111,c_2109])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2119,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2593,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2408,c_2119])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2117,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3856,plain,
    ( r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2593,c_2117])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2248,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2249,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2248])).

cnf(c_4024,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3856,c_27,c_2249])).

cnf(c_4025,plain,
    ( r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4024])).

cnf(c_15,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2118,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2703,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2593,c_2118])).

cnf(c_2792,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2703,c_27,c_2249])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2124,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3073,plain,
    ( k10_relat_1(sK3,X0) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2792,c_2124])).

cnf(c_4034,plain,
    ( k10_relat_1(sK3,X0) = k1_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4025,c_3073])).

cnf(c_4048,plain,
    ( k10_relat_1(sK3,sK2) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3766,c_4034])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2115,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3002,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2111,c_2115])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2114,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2482,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2111,c_2114])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) != k7_relset_1(sK1,sK2,sK3,sK1)
    | k1_relset_1(sK1,sK2,sK3) != k8_relset_1(sK1,sK2,sK3,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2600,plain,
    ( k8_relset_1(sK1,sK2,sK3,sK2) != k1_relset_1(sK1,sK2,sK3)
    | k7_relset_1(sK1,sK2,sK3,sK1) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2482,c_25])).

cnf(c_3309,plain,
    ( k8_relset_1(sK1,sK2,sK3,sK2) != k1_relat_1(sK3)
    | k7_relset_1(sK1,sK2,sK3,sK1) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3002,c_2600])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2112,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3127,plain,
    ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2111,c_2112])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2113,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3297,plain,
    ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2111,c_2113])).

cnf(c_3514,plain,
    ( k10_relat_1(sK3,sK2) != k1_relat_1(sK3)
    | k9_relat_1(sK3,sK1) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3309,c_3127,c_3297])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4510,c_4048,c_3514])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.41/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.41/1.05  
% 1.41/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.41/1.05  
% 1.41/1.05  ------  iProver source info
% 1.41/1.05  
% 1.41/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.41/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.41/1.05  git: non_committed_changes: false
% 1.41/1.05  git: last_make_outside_of_git: false
% 1.41/1.05  
% 1.41/1.05  ------ 
% 1.41/1.05  
% 1.41/1.05  ------ Input Options
% 1.41/1.05  
% 1.41/1.05  --out_options                           all
% 1.41/1.05  --tptp_safe_out                         true
% 1.41/1.05  --problem_path                          ""
% 1.41/1.05  --include_path                          ""
% 1.41/1.05  --clausifier                            res/vclausify_rel
% 1.41/1.05  --clausifier_options                    --mode clausify
% 1.41/1.05  --stdin                                 false
% 1.41/1.05  --stats_out                             all
% 1.41/1.05  
% 1.41/1.05  ------ General Options
% 1.41/1.05  
% 1.41/1.05  --fof                                   false
% 1.41/1.05  --time_out_real                         305.
% 1.41/1.05  --time_out_virtual                      -1.
% 1.41/1.05  --symbol_type_check                     false
% 1.41/1.05  --clausify_out                          false
% 1.41/1.05  --sig_cnt_out                           false
% 1.41/1.05  --trig_cnt_out                          false
% 1.41/1.05  --trig_cnt_out_tolerance                1.
% 1.41/1.05  --trig_cnt_out_sk_spl                   false
% 1.41/1.05  --abstr_cl_out                          false
% 1.41/1.05  
% 1.41/1.05  ------ Global Options
% 1.41/1.05  
% 1.41/1.05  --schedule                              default
% 1.41/1.05  --add_important_lit                     false
% 1.41/1.05  --prop_solver_per_cl                    1000
% 1.41/1.05  --min_unsat_core                        false
% 1.41/1.05  --soft_assumptions                      false
% 1.41/1.05  --soft_lemma_size                       3
% 1.41/1.05  --prop_impl_unit_size                   0
% 1.41/1.05  --prop_impl_unit                        []
% 1.41/1.05  --share_sel_clauses                     true
% 1.41/1.05  --reset_solvers                         false
% 1.41/1.05  --bc_imp_inh                            [conj_cone]
% 1.41/1.05  --conj_cone_tolerance                   3.
% 1.41/1.05  --extra_neg_conj                        none
% 1.41/1.05  --large_theory_mode                     true
% 1.41/1.05  --prolific_symb_bound                   200
% 1.41/1.05  --lt_threshold                          2000
% 1.41/1.05  --clause_weak_htbl                      true
% 1.41/1.05  --gc_record_bc_elim                     false
% 1.41/1.05  
% 1.41/1.05  ------ Preprocessing Options
% 1.41/1.05  
% 1.41/1.05  --preprocessing_flag                    true
% 1.41/1.05  --time_out_prep_mult                    0.1
% 1.41/1.05  --splitting_mode                        input
% 1.41/1.05  --splitting_grd                         true
% 1.41/1.05  --splitting_cvd                         false
% 1.41/1.05  --splitting_cvd_svl                     false
% 1.41/1.05  --splitting_nvd                         32
% 1.41/1.05  --sub_typing                            true
% 1.41/1.05  --prep_gs_sim                           true
% 1.41/1.05  --prep_unflatten                        true
% 1.41/1.05  --prep_res_sim                          true
% 1.41/1.05  --prep_upred                            true
% 1.41/1.05  --prep_sem_filter                       exhaustive
% 1.41/1.05  --prep_sem_filter_out                   false
% 1.41/1.05  --pred_elim                             true
% 1.41/1.05  --res_sim_input                         true
% 1.41/1.05  --eq_ax_congr_red                       true
% 1.41/1.05  --pure_diseq_elim                       true
% 1.41/1.05  --brand_transform                       false
% 1.41/1.05  --non_eq_to_eq                          false
% 1.41/1.05  --prep_def_merge                        true
% 1.41/1.05  --prep_def_merge_prop_impl              false
% 1.41/1.05  --prep_def_merge_mbd                    true
% 1.41/1.05  --prep_def_merge_tr_red                 false
% 1.41/1.05  --prep_def_merge_tr_cl                  false
% 1.41/1.05  --smt_preprocessing                     true
% 1.41/1.05  --smt_ac_axioms                         fast
% 1.41/1.05  --preprocessed_out                      false
% 1.41/1.05  --preprocessed_stats                    false
% 1.41/1.05  
% 1.41/1.05  ------ Abstraction refinement Options
% 1.41/1.05  
% 1.41/1.05  --abstr_ref                             []
% 1.41/1.05  --abstr_ref_prep                        false
% 1.41/1.05  --abstr_ref_until_sat                   false
% 1.41/1.05  --abstr_ref_sig_restrict                funpre
% 1.41/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.41/1.05  --abstr_ref_under                       []
% 1.41/1.05  
% 1.41/1.05  ------ SAT Options
% 1.41/1.05  
% 1.41/1.05  --sat_mode                              false
% 1.41/1.05  --sat_fm_restart_options                ""
% 1.41/1.05  --sat_gr_def                            false
% 1.41/1.05  --sat_epr_types                         true
% 1.41/1.05  --sat_non_cyclic_types                  false
% 1.41/1.05  --sat_finite_models                     false
% 1.41/1.05  --sat_fm_lemmas                         false
% 1.41/1.05  --sat_fm_prep                           false
% 1.41/1.05  --sat_fm_uc_incr                        true
% 1.41/1.05  --sat_out_model                         small
% 1.41/1.05  --sat_out_clauses                       false
% 1.41/1.05  
% 1.41/1.05  ------ QBF Options
% 1.41/1.05  
% 1.41/1.05  --qbf_mode                              false
% 1.41/1.05  --qbf_elim_univ                         false
% 1.41/1.05  --qbf_dom_inst                          none
% 1.41/1.05  --qbf_dom_pre_inst                      false
% 1.41/1.05  --qbf_sk_in                             false
% 1.41/1.05  --qbf_pred_elim                         true
% 1.41/1.05  --qbf_split                             512
% 1.41/1.05  
% 1.41/1.05  ------ BMC1 Options
% 1.41/1.05  
% 1.41/1.05  --bmc1_incremental                      false
% 1.41/1.05  --bmc1_axioms                           reachable_all
% 1.41/1.05  --bmc1_min_bound                        0
% 1.41/1.05  --bmc1_max_bound                        -1
% 1.41/1.05  --bmc1_max_bound_default                -1
% 1.41/1.05  --bmc1_symbol_reachability              true
% 1.41/1.05  --bmc1_property_lemmas                  false
% 1.41/1.05  --bmc1_k_induction                      false
% 1.41/1.05  --bmc1_non_equiv_states                 false
% 1.41/1.05  --bmc1_deadlock                         false
% 1.41/1.05  --bmc1_ucm                              false
% 1.41/1.05  --bmc1_add_unsat_core                   none
% 1.41/1.05  --bmc1_unsat_core_children              false
% 1.41/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.41/1.05  --bmc1_out_stat                         full
% 1.41/1.05  --bmc1_ground_init                      false
% 1.41/1.05  --bmc1_pre_inst_next_state              false
% 1.41/1.05  --bmc1_pre_inst_state                   false
% 1.41/1.05  --bmc1_pre_inst_reach_state             false
% 1.41/1.05  --bmc1_out_unsat_core                   false
% 1.41/1.05  --bmc1_aig_witness_out                  false
% 1.41/1.05  --bmc1_verbose                          false
% 1.41/1.05  --bmc1_dump_clauses_tptp                false
% 1.41/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.41/1.05  --bmc1_dump_file                        -
% 1.41/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.41/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.41/1.05  --bmc1_ucm_extend_mode                  1
% 1.41/1.05  --bmc1_ucm_init_mode                    2
% 1.41/1.05  --bmc1_ucm_cone_mode                    none
% 1.41/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.41/1.05  --bmc1_ucm_relax_model                  4
% 1.41/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.41/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.41/1.05  --bmc1_ucm_layered_model                none
% 1.41/1.05  --bmc1_ucm_max_lemma_size               10
% 1.41/1.05  
% 1.41/1.05  ------ AIG Options
% 1.41/1.05  
% 1.41/1.05  --aig_mode                              false
% 1.41/1.05  
% 1.41/1.05  ------ Instantiation Options
% 1.41/1.05  
% 1.41/1.05  --instantiation_flag                    true
% 1.41/1.05  --inst_sos_flag                         false
% 1.41/1.05  --inst_sos_phase                        true
% 1.41/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.41/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.41/1.05  --inst_lit_sel_side                     num_symb
% 1.41/1.05  --inst_solver_per_active                1400
% 1.41/1.05  --inst_solver_calls_frac                1.
% 1.41/1.05  --inst_passive_queue_type               priority_queues
% 1.41/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.41/1.05  --inst_passive_queues_freq              [25;2]
% 1.41/1.05  --inst_dismatching                      true
% 1.41/1.05  --inst_eager_unprocessed_to_passive     true
% 1.41/1.05  --inst_prop_sim_given                   true
% 1.41/1.05  --inst_prop_sim_new                     false
% 1.41/1.05  --inst_subs_new                         false
% 1.41/1.05  --inst_eq_res_simp                      false
% 1.41/1.05  --inst_subs_given                       false
% 1.41/1.05  --inst_orphan_elimination               true
% 1.41/1.05  --inst_learning_loop_flag               true
% 1.41/1.05  --inst_learning_start                   3000
% 1.41/1.05  --inst_learning_factor                  2
% 1.41/1.05  --inst_start_prop_sim_after_learn       3
% 1.41/1.05  --inst_sel_renew                        solver
% 1.41/1.05  --inst_lit_activity_flag                true
% 1.41/1.05  --inst_restr_to_given                   false
% 1.41/1.05  --inst_activity_threshold               500
% 1.41/1.05  --inst_out_proof                        true
% 1.41/1.05  
% 1.41/1.05  ------ Resolution Options
% 1.41/1.05  
% 1.41/1.05  --resolution_flag                       true
% 1.41/1.05  --res_lit_sel                           adaptive
% 1.41/1.05  --res_lit_sel_side                      none
% 1.41/1.05  --res_ordering                          kbo
% 1.41/1.05  --res_to_prop_solver                    active
% 1.41/1.05  --res_prop_simpl_new                    false
% 1.41/1.05  --res_prop_simpl_given                  true
% 1.41/1.05  --res_passive_queue_type                priority_queues
% 1.41/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.41/1.05  --res_passive_queues_freq               [15;5]
% 1.41/1.05  --res_forward_subs                      full
% 1.41/1.05  --res_backward_subs                     full
% 1.41/1.05  --res_forward_subs_resolution           true
% 1.41/1.05  --res_backward_subs_resolution          true
% 1.41/1.05  --res_orphan_elimination                true
% 1.41/1.05  --res_time_limit                        2.
% 1.41/1.05  --res_out_proof                         true
% 1.41/1.05  
% 1.41/1.05  ------ Superposition Options
% 1.41/1.05  
% 1.41/1.05  --superposition_flag                    true
% 1.41/1.05  --sup_passive_queue_type                priority_queues
% 1.41/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.41/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.41/1.05  --demod_completeness_check              fast
% 1.41/1.05  --demod_use_ground                      true
% 1.41/1.05  --sup_to_prop_solver                    passive
% 1.41/1.05  --sup_prop_simpl_new                    true
% 1.41/1.05  --sup_prop_simpl_given                  true
% 1.41/1.05  --sup_fun_splitting                     false
% 1.41/1.05  --sup_smt_interval                      50000
% 1.41/1.05  
% 1.41/1.05  ------ Superposition Simplification Setup
% 1.41/1.05  
% 1.41/1.05  --sup_indices_passive                   []
% 1.41/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.41/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.05  --sup_full_bw                           [BwDemod]
% 1.41/1.05  --sup_immed_triv                        [TrivRules]
% 1.41/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.41/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.05  --sup_immed_bw_main                     []
% 1.41/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.41/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.05  
% 1.41/1.05  ------ Combination Options
% 1.41/1.05  
% 1.41/1.05  --comb_res_mult                         3
% 1.41/1.05  --comb_sup_mult                         2
% 1.41/1.05  --comb_inst_mult                        10
% 1.41/1.05  
% 1.41/1.05  ------ Debug Options
% 1.41/1.05  
% 1.41/1.05  --dbg_backtrace                         false
% 1.41/1.05  --dbg_dump_prop_clauses                 false
% 1.41/1.05  --dbg_dump_prop_clauses_file            -
% 1.41/1.05  --dbg_out_stat                          false
% 1.41/1.05  ------ Parsing...
% 1.41/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.41/1.05  
% 1.41/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.41/1.05  
% 1.41/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.41/1.05  
% 1.41/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.41/1.05  ------ Proving...
% 1.41/1.05  ------ Problem Properties 
% 1.41/1.05  
% 1.41/1.05  
% 1.41/1.05  clauses                                 19
% 1.41/1.05  conjectures                             2
% 1.41/1.05  EPR                                     2
% 1.41/1.05  Horn                                    18
% 1.41/1.05  unary                                   2
% 1.41/1.05  binary                                  13
% 1.41/1.05  lits                                    40
% 1.41/1.05  lits eq                                 12
% 1.41/1.05  fd_pure                                 0
% 1.41/1.05  fd_pseudo                               0
% 1.41/1.05  fd_cond                                 0
% 1.41/1.05  fd_pseudo_cond                          1
% 1.41/1.05  AC symbols                              0
% 1.41/1.05  
% 1.41/1.05  ------ Schedule dynamic 5 is on 
% 1.41/1.05  
% 1.41/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.41/1.05  
% 1.41/1.05  
% 1.41/1.05  ------ 
% 1.41/1.05  Current options:
% 1.41/1.05  ------ 
% 1.41/1.05  
% 1.41/1.05  ------ Input Options
% 1.41/1.05  
% 1.41/1.05  --out_options                           all
% 1.41/1.05  --tptp_safe_out                         true
% 1.41/1.05  --problem_path                          ""
% 1.41/1.05  --include_path                          ""
% 1.41/1.05  --clausifier                            res/vclausify_rel
% 1.41/1.05  --clausifier_options                    --mode clausify
% 1.41/1.05  --stdin                                 false
% 1.41/1.05  --stats_out                             all
% 1.41/1.05  
% 1.41/1.05  ------ General Options
% 1.41/1.05  
% 1.41/1.05  --fof                                   false
% 1.41/1.05  --time_out_real                         305.
% 1.41/1.05  --time_out_virtual                      -1.
% 1.41/1.05  --symbol_type_check                     false
% 1.41/1.05  --clausify_out                          false
% 1.41/1.05  --sig_cnt_out                           false
% 1.41/1.05  --trig_cnt_out                          false
% 1.41/1.05  --trig_cnt_out_tolerance                1.
% 1.41/1.05  --trig_cnt_out_sk_spl                   false
% 1.41/1.05  --abstr_cl_out                          false
% 1.41/1.05  
% 1.41/1.05  ------ Global Options
% 1.41/1.05  
% 1.41/1.05  --schedule                              default
% 1.41/1.05  --add_important_lit                     false
% 1.41/1.05  --prop_solver_per_cl                    1000
% 1.41/1.05  --min_unsat_core                        false
% 1.41/1.05  --soft_assumptions                      false
% 1.41/1.05  --soft_lemma_size                       3
% 1.41/1.05  --prop_impl_unit_size                   0
% 1.41/1.05  --prop_impl_unit                        []
% 1.41/1.05  --share_sel_clauses                     true
% 1.41/1.05  --reset_solvers                         false
% 1.41/1.05  --bc_imp_inh                            [conj_cone]
% 1.41/1.05  --conj_cone_tolerance                   3.
% 1.41/1.05  --extra_neg_conj                        none
% 1.41/1.05  --large_theory_mode                     true
% 1.41/1.05  --prolific_symb_bound                   200
% 1.41/1.05  --lt_threshold                          2000
% 1.41/1.05  --clause_weak_htbl                      true
% 1.41/1.05  --gc_record_bc_elim                     false
% 1.41/1.05  
% 1.41/1.05  ------ Preprocessing Options
% 1.41/1.05  
% 1.41/1.05  --preprocessing_flag                    true
% 1.41/1.05  --time_out_prep_mult                    0.1
% 1.41/1.05  --splitting_mode                        input
% 1.41/1.05  --splitting_grd                         true
% 1.41/1.05  --splitting_cvd                         false
% 1.41/1.05  --splitting_cvd_svl                     false
% 1.41/1.05  --splitting_nvd                         32
% 1.41/1.05  --sub_typing                            true
% 1.41/1.05  --prep_gs_sim                           true
% 1.41/1.05  --prep_unflatten                        true
% 1.41/1.05  --prep_res_sim                          true
% 1.41/1.05  --prep_upred                            true
% 1.41/1.05  --prep_sem_filter                       exhaustive
% 1.41/1.05  --prep_sem_filter_out                   false
% 1.41/1.05  --pred_elim                             true
% 1.41/1.05  --res_sim_input                         true
% 1.41/1.05  --eq_ax_congr_red                       true
% 1.41/1.05  --pure_diseq_elim                       true
% 1.41/1.05  --brand_transform                       false
% 1.41/1.05  --non_eq_to_eq                          false
% 1.41/1.05  --prep_def_merge                        true
% 1.41/1.05  --prep_def_merge_prop_impl              false
% 1.41/1.05  --prep_def_merge_mbd                    true
% 1.41/1.05  --prep_def_merge_tr_red                 false
% 1.41/1.05  --prep_def_merge_tr_cl                  false
% 1.41/1.05  --smt_preprocessing                     true
% 1.41/1.05  --smt_ac_axioms                         fast
% 1.41/1.05  --preprocessed_out                      false
% 1.41/1.05  --preprocessed_stats                    false
% 1.41/1.05  
% 1.41/1.05  ------ Abstraction refinement Options
% 1.41/1.05  
% 1.41/1.05  --abstr_ref                             []
% 1.41/1.05  --abstr_ref_prep                        false
% 1.41/1.05  --abstr_ref_until_sat                   false
% 1.41/1.05  --abstr_ref_sig_restrict                funpre
% 1.41/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.41/1.05  --abstr_ref_under                       []
% 1.41/1.05  
% 1.41/1.05  ------ SAT Options
% 1.41/1.05  
% 1.41/1.05  --sat_mode                              false
% 1.41/1.05  --sat_fm_restart_options                ""
% 1.41/1.05  --sat_gr_def                            false
% 1.41/1.05  --sat_epr_types                         true
% 1.41/1.05  --sat_non_cyclic_types                  false
% 1.41/1.05  --sat_finite_models                     false
% 1.41/1.05  --sat_fm_lemmas                         false
% 1.41/1.05  --sat_fm_prep                           false
% 1.41/1.05  --sat_fm_uc_incr                        true
% 1.41/1.05  --sat_out_model                         small
% 1.41/1.05  --sat_out_clauses                       false
% 1.41/1.05  
% 1.41/1.05  ------ QBF Options
% 1.41/1.05  
% 1.41/1.05  --qbf_mode                              false
% 1.41/1.05  --qbf_elim_univ                         false
% 1.41/1.05  --qbf_dom_inst                          none
% 1.41/1.05  --qbf_dom_pre_inst                      false
% 1.41/1.05  --qbf_sk_in                             false
% 1.41/1.05  --qbf_pred_elim                         true
% 1.41/1.05  --qbf_split                             512
% 1.41/1.05  
% 1.41/1.05  ------ BMC1 Options
% 1.41/1.05  
% 1.41/1.05  --bmc1_incremental                      false
% 1.41/1.05  --bmc1_axioms                           reachable_all
% 1.41/1.05  --bmc1_min_bound                        0
% 1.41/1.05  --bmc1_max_bound                        -1
% 1.41/1.05  --bmc1_max_bound_default                -1
% 1.41/1.05  --bmc1_symbol_reachability              true
% 1.41/1.05  --bmc1_property_lemmas                  false
% 1.41/1.05  --bmc1_k_induction                      false
% 1.41/1.05  --bmc1_non_equiv_states                 false
% 1.41/1.05  --bmc1_deadlock                         false
% 1.41/1.05  --bmc1_ucm                              false
% 1.41/1.05  --bmc1_add_unsat_core                   none
% 1.41/1.05  --bmc1_unsat_core_children              false
% 1.41/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.41/1.05  --bmc1_out_stat                         full
% 1.41/1.05  --bmc1_ground_init                      false
% 1.41/1.05  --bmc1_pre_inst_next_state              false
% 1.41/1.05  --bmc1_pre_inst_state                   false
% 1.41/1.05  --bmc1_pre_inst_reach_state             false
% 1.41/1.05  --bmc1_out_unsat_core                   false
% 1.41/1.05  --bmc1_aig_witness_out                  false
% 1.41/1.05  --bmc1_verbose                          false
% 1.41/1.05  --bmc1_dump_clauses_tptp                false
% 1.41/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.41/1.05  --bmc1_dump_file                        -
% 1.41/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.41/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.41/1.05  --bmc1_ucm_extend_mode                  1
% 1.41/1.05  --bmc1_ucm_init_mode                    2
% 1.41/1.05  --bmc1_ucm_cone_mode                    none
% 1.41/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.41/1.05  --bmc1_ucm_relax_model                  4
% 1.41/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.41/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.41/1.05  --bmc1_ucm_layered_model                none
% 1.41/1.05  --bmc1_ucm_max_lemma_size               10
% 1.41/1.05  
% 1.41/1.05  ------ AIG Options
% 1.41/1.05  
% 1.41/1.05  --aig_mode                              false
% 1.41/1.05  
% 1.41/1.05  ------ Instantiation Options
% 1.41/1.05  
% 1.41/1.05  --instantiation_flag                    true
% 1.41/1.05  --inst_sos_flag                         false
% 1.41/1.05  --inst_sos_phase                        true
% 1.41/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.41/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.41/1.05  --inst_lit_sel_side                     none
% 1.41/1.05  --inst_solver_per_active                1400
% 1.41/1.05  --inst_solver_calls_frac                1.
% 1.41/1.05  --inst_passive_queue_type               priority_queues
% 1.41/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.41/1.05  --inst_passive_queues_freq              [25;2]
% 1.41/1.05  --inst_dismatching                      true
% 1.41/1.05  --inst_eager_unprocessed_to_passive     true
% 1.41/1.05  --inst_prop_sim_given                   true
% 1.41/1.05  --inst_prop_sim_new                     false
% 1.41/1.05  --inst_subs_new                         false
% 1.41/1.05  --inst_eq_res_simp                      false
% 1.41/1.05  --inst_subs_given                       false
% 1.41/1.05  --inst_orphan_elimination               true
% 1.41/1.05  --inst_learning_loop_flag               true
% 1.41/1.05  --inst_learning_start                   3000
% 1.41/1.05  --inst_learning_factor                  2
% 1.41/1.05  --inst_start_prop_sim_after_learn       3
% 1.41/1.05  --inst_sel_renew                        solver
% 1.41/1.05  --inst_lit_activity_flag                true
% 1.41/1.05  --inst_restr_to_given                   false
% 1.41/1.05  --inst_activity_threshold               500
% 1.41/1.05  --inst_out_proof                        true
% 1.41/1.05  
% 1.41/1.05  ------ Resolution Options
% 1.41/1.05  
% 1.41/1.05  --resolution_flag                       false
% 1.41/1.05  --res_lit_sel                           adaptive
% 1.41/1.05  --res_lit_sel_side                      none
% 1.41/1.05  --res_ordering                          kbo
% 1.41/1.05  --res_to_prop_solver                    active
% 1.41/1.05  --res_prop_simpl_new                    false
% 1.41/1.05  --res_prop_simpl_given                  true
% 1.41/1.05  --res_passive_queue_type                priority_queues
% 1.41/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.41/1.05  --res_passive_queues_freq               [15;5]
% 1.41/1.05  --res_forward_subs                      full
% 1.41/1.05  --res_backward_subs                     full
% 1.41/1.05  --res_forward_subs_resolution           true
% 1.41/1.05  --res_backward_subs_resolution          true
% 1.41/1.05  --res_orphan_elimination                true
% 1.41/1.05  --res_time_limit                        2.
% 1.41/1.05  --res_out_proof                         true
% 1.41/1.05  
% 1.41/1.05  ------ Superposition Options
% 1.41/1.05  
% 1.41/1.05  --superposition_flag                    true
% 1.41/1.05  --sup_passive_queue_type                priority_queues
% 1.41/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.41/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.49/1.05  --demod_completeness_check              fast
% 1.49/1.05  --demod_use_ground                      true
% 1.49/1.05  --sup_to_prop_solver                    passive
% 1.49/1.05  --sup_prop_simpl_new                    true
% 1.49/1.05  --sup_prop_simpl_given                  true
% 1.49/1.05  --sup_fun_splitting                     false
% 1.49/1.05  --sup_smt_interval                      50000
% 1.49/1.05  
% 1.49/1.05  ------ Superposition Simplification Setup
% 1.49/1.05  
% 1.49/1.05  --sup_indices_passive                   []
% 1.49/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.49/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.05  --sup_full_bw                           [BwDemod]
% 1.49/1.05  --sup_immed_triv                        [TrivRules]
% 1.49/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.49/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.05  --sup_immed_bw_main                     []
% 1.49/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.49/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.49/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.49/1.05  
% 1.49/1.05  ------ Combination Options
% 1.49/1.05  
% 1.49/1.05  --comb_res_mult                         3
% 1.49/1.05  --comb_sup_mult                         2
% 1.49/1.05  --comb_inst_mult                        10
% 1.49/1.05  
% 1.49/1.05  ------ Debug Options
% 1.49/1.05  
% 1.49/1.05  --dbg_backtrace                         false
% 1.49/1.05  --dbg_dump_prop_clauses                 false
% 1.49/1.05  --dbg_dump_prop_clauses_file            -
% 1.49/1.05  --dbg_out_stat                          false
% 1.49/1.05  
% 1.49/1.05  
% 1.49/1.05  
% 1.49/1.05  
% 1.49/1.05  ------ Proving...
% 1.49/1.05  
% 1.49/1.05  
% 1.49/1.05  % SZS status Theorem for theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  fof(f18,conjecture,(
% 1.49/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.49/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.05  
% 1.49/1.05  fof(f19,negated_conjecture,(
% 1.49/1.05    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.49/1.05    inference(negated_conjecture,[],[f18])).
% 1.49/1.05  
% 1.49/1.05  fof(f36,plain,(
% 1.49/1.05    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/1.05    inference(ennf_transformation,[],[f19])).
% 1.49/1.05  
% 1.49/1.05  fof(f45,plain,(
% 1.49/1.05    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK1,sK2,sK3) != k8_relset_1(sK1,sK2,sK3,sK2) | k2_relset_1(sK1,sK2,sK3) != k7_relset_1(sK1,sK2,sK3,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 1.49/1.05    introduced(choice_axiom,[])).
% 1.49/1.05  
% 1.49/1.05  fof(f46,plain,(
% 1.49/1.05    (k1_relset_1(sK1,sK2,sK3) != k8_relset_1(sK1,sK2,sK3,sK2) | k2_relset_1(sK1,sK2,sK3) != k7_relset_1(sK1,sK2,sK3,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f45])).
% 1.49/1.05  
% 1.49/1.05  fof(f72,plain,(
% 1.49/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/1.05    inference(cnf_transformation,[],[f46])).
% 1.49/1.05  
% 1.49/1.05  fof(f13,axiom,(
% 1.49/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.49/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.05  
% 1.49/1.05  fof(f31,plain,(
% 1.49/1.05    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/1.05    inference(ennf_transformation,[],[f13])).
% 1.49/1.05  
% 1.49/1.05  fof(f66,plain,(
% 1.49/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/1.05    inference(cnf_transformation,[],[f31])).
% 1.49/1.05  
% 1.49/1.05  fof(f11,axiom,(
% 1.49/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.49/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.05  
% 1.49/1.05  fof(f28,plain,(
% 1.49/1.05    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.49/1.05    inference(ennf_transformation,[],[f11])).
% 1.49/1.05  
% 1.49/1.05  fof(f29,plain,(
% 1.49/1.05    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.49/1.05    inference(flattening,[],[f28])).
% 1.49/1.05  
% 1.49/1.05  fof(f64,plain,(
% 1.49/1.05    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.49/1.05    inference(cnf_transformation,[],[f29])).
% 1.49/1.05  
% 1.49/1.05  fof(f12,axiom,(
% 1.49/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.49/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.05  
% 1.49/1.05  fof(f30,plain,(
% 1.49/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/1.05    inference(ennf_transformation,[],[f12])).
% 1.49/1.05  
% 1.49/1.05  fof(f65,plain,(
% 1.49/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/1.06    inference(cnf_transformation,[],[f30])).
% 1.49/1.06  
% 1.49/1.06  fof(f7,axiom,(
% 1.49/1.06    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f23,plain,(
% 1.49/1.06    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.49/1.06    inference(ennf_transformation,[],[f7])).
% 1.49/1.06  
% 1.49/1.06  fof(f60,plain,(
% 1.49/1.06    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.49/1.06    inference(cnf_transformation,[],[f23])).
% 1.49/1.06  
% 1.49/1.06  fof(f67,plain,(
% 1.49/1.06    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/1.06    inference(cnf_transformation,[],[f31])).
% 1.49/1.06  
% 1.49/1.06  fof(f6,axiom,(
% 1.49/1.06    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f22,plain,(
% 1.49/1.06    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/1.06    inference(ennf_transformation,[],[f6])).
% 1.49/1.06  
% 1.49/1.06  fof(f44,plain,(
% 1.49/1.06    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.49/1.06    inference(nnf_transformation,[],[f22])).
% 1.49/1.06  
% 1.49/1.06  fof(f58,plain,(
% 1.49/1.06    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.49/1.06    inference(cnf_transformation,[],[f44])).
% 1.49/1.06  
% 1.49/1.06  fof(f8,axiom,(
% 1.49/1.06    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f24,plain,(
% 1.49/1.06    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.49/1.06    inference(ennf_transformation,[],[f8])).
% 1.49/1.06  
% 1.49/1.06  fof(f61,plain,(
% 1.49/1.06    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/1.06    inference(cnf_transformation,[],[f24])).
% 1.49/1.06  
% 1.49/1.06  fof(f10,axiom,(
% 1.49/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f26,plain,(
% 1.49/1.06    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.49/1.06    inference(ennf_transformation,[],[f10])).
% 1.49/1.06  
% 1.49/1.06  fof(f27,plain,(
% 1.49/1.06    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.49/1.06    inference(flattening,[],[f26])).
% 1.49/1.06  
% 1.49/1.06  fof(f63,plain,(
% 1.49/1.06    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.49/1.06    inference(cnf_transformation,[],[f27])).
% 1.49/1.06  
% 1.49/1.06  fof(f9,axiom,(
% 1.49/1.06    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f25,plain,(
% 1.49/1.06    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.49/1.06    inference(ennf_transformation,[],[f9])).
% 1.49/1.06  
% 1.49/1.06  fof(f62,plain,(
% 1.49/1.06    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.49/1.06    inference(cnf_transformation,[],[f25])).
% 1.49/1.06  
% 1.49/1.06  fof(f1,axiom,(
% 1.49/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f37,plain,(
% 1.49/1.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/1.06    inference(nnf_transformation,[],[f1])).
% 1.49/1.06  
% 1.49/1.06  fof(f38,plain,(
% 1.49/1.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/1.06    inference(flattening,[],[f37])).
% 1.49/1.06  
% 1.49/1.06  fof(f49,plain,(
% 1.49/1.06    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.49/1.06    inference(cnf_transformation,[],[f38])).
% 1.49/1.06  
% 1.49/1.06  fof(f14,axiom,(
% 1.49/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f32,plain,(
% 1.49/1.06    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/1.06    inference(ennf_transformation,[],[f14])).
% 1.49/1.06  
% 1.49/1.06  fof(f68,plain,(
% 1.49/1.06    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/1.06    inference(cnf_transformation,[],[f32])).
% 1.49/1.06  
% 1.49/1.06  fof(f15,axiom,(
% 1.49/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f33,plain,(
% 1.49/1.06    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/1.06    inference(ennf_transformation,[],[f15])).
% 1.49/1.06  
% 1.49/1.06  fof(f69,plain,(
% 1.49/1.06    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/1.06    inference(cnf_transformation,[],[f33])).
% 1.49/1.06  
% 1.49/1.06  fof(f73,plain,(
% 1.49/1.06    k1_relset_1(sK1,sK2,sK3) != k8_relset_1(sK1,sK2,sK3,sK2) | k2_relset_1(sK1,sK2,sK3) != k7_relset_1(sK1,sK2,sK3,sK1)),
% 1.49/1.06    inference(cnf_transformation,[],[f46])).
% 1.49/1.06  
% 1.49/1.06  fof(f17,axiom,(
% 1.49/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f35,plain,(
% 1.49/1.06    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/1.06    inference(ennf_transformation,[],[f17])).
% 1.49/1.06  
% 1.49/1.06  fof(f71,plain,(
% 1.49/1.06    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/1.06    inference(cnf_transformation,[],[f35])).
% 1.49/1.06  
% 1.49/1.06  fof(f16,axiom,(
% 1.49/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.49/1.06  
% 1.49/1.06  fof(f34,plain,(
% 1.49/1.06    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/1.06    inference(ennf_transformation,[],[f16])).
% 1.49/1.06  
% 1.49/1.06  fof(f70,plain,(
% 1.49/1.06    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/1.06    inference(cnf_transformation,[],[f34])).
% 1.49/1.06  
% 1.49/1.06  cnf(c_26,negated_conjecture,
% 1.49/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.49/1.06      inference(cnf_transformation,[],[f72]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2111,plain,
% 1.49/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_20,plain,
% 1.49/1.06      ( v4_relat_1(X0,X1)
% 1.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.49/1.06      inference(cnf_transformation,[],[f66]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_17,plain,
% 1.49/1.06      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.49/1.06      inference(cnf_transformation,[],[f64]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_376,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | ~ v1_relat_1(X0)
% 1.49/1.06      | k7_relat_1(X0,X1) = X0 ),
% 1.49/1.06      inference(resolution,[status(thm)],[c_20,c_17]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_18,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | v1_relat_1(X0) ),
% 1.49/1.06      inference(cnf_transformation,[],[f65]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_380,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | k7_relat_1(X0,X1) = X0 ),
% 1.49/1.06      inference(global_propositional_subsumption,
% 1.49/1.06                [status(thm)],
% 1.49/1.06                [c_376,c_20,c_18,c_17]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2110,plain,
% 1.49/1.06      ( k7_relat_1(X0,X1) = X0
% 1.49/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_4398,plain,
% 1.49/1.06      ( k7_relat_1(sK3,sK1) = sK3 ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2111,c_2110]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2116,plain,
% 1.49/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.49/1.06      | v1_relat_1(X0) = iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2408,plain,
% 1.49/1.06      ( v1_relat_1(sK3) = iProver_top ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2111,c_2116]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_13,plain,
% 1.49/1.06      ( ~ v1_relat_1(X0)
% 1.49/1.06      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 1.49/1.06      inference(cnf_transformation,[],[f60]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2120,plain,
% 1.49/1.06      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 1.49/1.06      | v1_relat_1(X0) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2592,plain,
% 1.49/1.06      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2408,c_2120]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_4510,plain,
% 1.49/1.06      ( k9_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_4398,c_2592]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_19,plain,
% 1.49/1.06      ( v5_relat_1(X0,X1)
% 1.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.49/1.06      inference(cnf_transformation,[],[f67]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_12,plain,
% 1.49/1.06      ( ~ v5_relat_1(X0,X1)
% 1.49/1.06      | r1_tarski(k2_relat_1(X0),X1)
% 1.49/1.06      | ~ v1_relat_1(X0) ),
% 1.49/1.06      inference(cnf_transformation,[],[f58]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_396,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | r1_tarski(k2_relat_1(X0),X2)
% 1.49/1.06      | ~ v1_relat_1(X0) ),
% 1.49/1.06      inference(resolution,[status(thm)],[c_19,c_12]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_400,plain,
% 1.49/1.06      ( r1_tarski(k2_relat_1(X0),X2)
% 1.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.49/1.06      inference(global_propositional_subsumption,
% 1.49/1.06                [status(thm)],
% 1.49/1.06                [c_396,c_18]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_401,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | r1_tarski(k2_relat_1(X0),X2) ),
% 1.49/1.06      inference(renaming,[status(thm)],[c_400]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2109,plain,
% 1.49/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.49/1.06      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_3766,plain,
% 1.49/1.06      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2111,c_2109]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_14,plain,
% 1.49/1.06      ( ~ v1_relat_1(X0)
% 1.49/1.06      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 1.49/1.06      inference(cnf_transformation,[],[f61]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2119,plain,
% 1.49/1.06      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 1.49/1.06      | v1_relat_1(X0) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2593,plain,
% 1.49/1.06      ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2408,c_2119]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_16,plain,
% 1.49/1.06      ( ~ r1_tarski(X0,X1)
% 1.49/1.06      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
% 1.49/1.06      | ~ v1_relat_1(X2) ),
% 1.49/1.06      inference(cnf_transformation,[],[f63]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2117,plain,
% 1.49/1.06      ( r1_tarski(X0,X1) != iProver_top
% 1.49/1.06      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
% 1.49/1.06      | v1_relat_1(X2) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_3856,plain,
% 1.49/1.06      ( r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,X0)) = iProver_top
% 1.49/1.06      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 1.49/1.06      | v1_relat_1(sK3) != iProver_top ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2593,c_2117]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_27,plain,
% 1.49/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2248,plain,
% 1.49/1.06      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.49/1.06      | v1_relat_1(sK3) ),
% 1.49/1.06      inference(instantiation,[status(thm)],[c_18]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2249,plain,
% 1.49/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.49/1.06      | v1_relat_1(sK3) = iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_2248]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_4024,plain,
% 1.49/1.06      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 1.49/1.06      | r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,X0)) = iProver_top ),
% 1.49/1.06      inference(global_propositional_subsumption,
% 1.49/1.06                [status(thm)],
% 1.49/1.06                [c_3856,c_27,c_2249]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_4025,plain,
% 1.49/1.06      ( r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,X0)) = iProver_top
% 1.49/1.06      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 1.49/1.06      inference(renaming,[status(thm)],[c_4024]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_15,plain,
% 1.49/1.06      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
% 1.49/1.06      | ~ v1_relat_1(X0) ),
% 1.49/1.06      inference(cnf_transformation,[],[f62]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2118,plain,
% 1.49/1.06      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
% 1.49/1.06      | v1_relat_1(X0) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2703,plain,
% 1.49/1.06      ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) = iProver_top
% 1.49/1.06      | v1_relat_1(sK3) != iProver_top ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2593,c_2118]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2792,plain,
% 1.49/1.06      ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) = iProver_top ),
% 1.49/1.06      inference(global_propositional_subsumption,
% 1.49/1.06                [status(thm)],
% 1.49/1.06                [c_2703,c_27,c_2249]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_0,plain,
% 1.49/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.49/1.06      inference(cnf_transformation,[],[f49]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2124,plain,
% 1.49/1.06      ( X0 = X1
% 1.49/1.06      | r1_tarski(X0,X1) != iProver_top
% 1.49/1.06      | r1_tarski(X1,X0) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_3073,plain,
% 1.49/1.06      ( k10_relat_1(sK3,X0) = k1_relat_1(sK3)
% 1.49/1.06      | r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,X0)) != iProver_top ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2792,c_2124]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_4034,plain,
% 1.49/1.06      ( k10_relat_1(sK3,X0) = k1_relat_1(sK3)
% 1.49/1.06      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_4025,c_3073]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_4048,plain,
% 1.49/1.06      ( k10_relat_1(sK3,sK2) = k1_relat_1(sK3) ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_3766,c_4034]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_21,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.49/1.06      inference(cnf_transformation,[],[f68]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2115,plain,
% 1.49/1.06      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.49/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_3002,plain,
% 1.49/1.06      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2111,c_2115]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_22,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.49/1.06      inference(cnf_transformation,[],[f69]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2114,plain,
% 1.49/1.06      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.49/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2482,plain,
% 1.49/1.06      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2111,c_2114]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_25,negated_conjecture,
% 1.49/1.06      ( k2_relset_1(sK1,sK2,sK3) != k7_relset_1(sK1,sK2,sK3,sK1)
% 1.49/1.06      | k1_relset_1(sK1,sK2,sK3) != k8_relset_1(sK1,sK2,sK3,sK2) ),
% 1.49/1.06      inference(cnf_transformation,[],[f73]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2600,plain,
% 1.49/1.06      ( k8_relset_1(sK1,sK2,sK3,sK2) != k1_relset_1(sK1,sK2,sK3)
% 1.49/1.06      | k7_relset_1(sK1,sK2,sK3,sK1) != k2_relat_1(sK3) ),
% 1.49/1.06      inference(demodulation,[status(thm)],[c_2482,c_25]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_3309,plain,
% 1.49/1.06      ( k8_relset_1(sK1,sK2,sK3,sK2) != k1_relat_1(sK3)
% 1.49/1.06      | k7_relset_1(sK1,sK2,sK3,sK1) != k2_relat_1(sK3) ),
% 1.49/1.06      inference(demodulation,[status(thm)],[c_3002,c_2600]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_24,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.49/1.06      inference(cnf_transformation,[],[f71]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2112,plain,
% 1.49/1.06      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.49/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_3127,plain,
% 1.49/1.06      ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2111,c_2112]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_23,plain,
% 1.49/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.06      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.49/1.06      inference(cnf_transformation,[],[f70]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_2113,plain,
% 1.49/1.06      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.49/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.49/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_3297,plain,
% 1.49/1.06      ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
% 1.49/1.06      inference(superposition,[status(thm)],[c_2111,c_2113]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(c_3514,plain,
% 1.49/1.06      ( k10_relat_1(sK3,sK2) != k1_relat_1(sK3)
% 1.49/1.06      | k9_relat_1(sK3,sK1) != k2_relat_1(sK3) ),
% 1.49/1.06      inference(demodulation,[status(thm)],[c_3309,c_3127,c_3297]) ).
% 1.49/1.06  
% 1.49/1.06  cnf(contradiction,plain,
% 1.49/1.06      ( $false ),
% 1.49/1.06      inference(minisat,[status(thm)],[c_4510,c_4048,c_3514]) ).
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.49/1.06  
% 1.49/1.06  ------                               Statistics
% 1.49/1.06  
% 1.49/1.06  ------ General
% 1.49/1.06  
% 1.49/1.06  abstr_ref_over_cycles:                  0
% 1.49/1.06  abstr_ref_under_cycles:                 0
% 1.49/1.06  gc_basic_clause_elim:                   0
% 1.49/1.06  forced_gc_time:                         0
% 1.49/1.06  parsing_time:                           0.017
% 1.49/1.06  unif_index_cands_time:                  0.
% 1.49/1.06  unif_index_add_time:                    0.
% 1.49/1.06  orderings_time:                         0.
% 1.49/1.06  out_proof_time:                         0.007
% 1.49/1.06  total_time:                             0.172
% 1.49/1.06  num_of_symbols:                         53
% 1.49/1.06  num_of_terms:                           3104
% 1.49/1.06  
% 1.49/1.06  ------ Preprocessing
% 1.49/1.06  
% 1.49/1.06  num_of_splits:                          0
% 1.49/1.06  num_of_split_atoms:                     0
% 1.49/1.06  num_of_reused_defs:                     0
% 1.49/1.06  num_eq_ax_congr_red:                    38
% 1.49/1.06  num_of_sem_filtered_clauses:            1
% 1.49/1.06  num_of_subtypes:                        0
% 1.49/1.06  monotx_restored_types:                  0
% 1.49/1.06  sat_num_of_epr_types:                   0
% 1.49/1.06  sat_num_of_non_cyclic_types:            0
% 1.49/1.06  sat_guarded_non_collapsed_types:        0
% 1.49/1.06  num_pure_diseq_elim:                    0
% 1.49/1.06  simp_replaced_by:                       0
% 1.49/1.06  res_preprocessed:                       131
% 1.49/1.06  prep_upred:                             0
% 1.49/1.06  prep_unflattend:                        60
% 1.49/1.06  smt_new_axioms:                         0
% 1.49/1.06  pred_elim_cands:                        3
% 1.49/1.06  pred_elim:                              4
% 1.49/1.06  pred_elim_cl:                           6
% 1.49/1.06  pred_elim_cycles:                       11
% 1.49/1.06  merged_defs:                            14
% 1.49/1.06  merged_defs_ncl:                        0
% 1.49/1.06  bin_hyper_res:                          15
% 1.49/1.06  prep_cycles:                            5
% 1.49/1.06  pred_elim_time:                         0.021
% 1.49/1.06  splitting_time:                         0.
% 1.49/1.06  sem_filter_time:                        0.
% 1.49/1.06  monotx_time:                            0.001
% 1.49/1.06  subtype_inf_time:                       0.
% 1.49/1.06  
% 1.49/1.06  ------ Problem properties
% 1.49/1.06  
% 1.49/1.06  clauses:                                19
% 1.49/1.06  conjectures:                            2
% 1.49/1.06  epr:                                    2
% 1.49/1.06  horn:                                   18
% 1.49/1.06  ground:                                 2
% 1.49/1.06  unary:                                  2
% 1.49/1.06  binary:                                 13
% 1.49/1.06  lits:                                   40
% 1.49/1.06  lits_eq:                                12
% 1.49/1.06  fd_pure:                                0
% 1.49/1.06  fd_pseudo:                              0
% 1.49/1.06  fd_cond:                                0
% 1.49/1.06  fd_pseudo_cond:                         1
% 1.49/1.06  ac_symbols:                             0
% 1.49/1.06  
% 1.49/1.06  ------ Propositional Solver
% 1.49/1.06  
% 1.49/1.06  prop_solver_calls:                      33
% 1.49/1.06  prop_fast_solver_calls:                 871
% 1.49/1.06  smt_solver_calls:                       0
% 1.49/1.06  smt_fast_solver_calls:                  0
% 1.49/1.06  prop_num_of_clauses:                    1330
% 1.49/1.06  prop_preprocess_simplified:             5447
% 1.49/1.06  prop_fo_subsumed:                       5
% 1.49/1.06  prop_solver_time:                       0.
% 1.49/1.06  smt_solver_time:                        0.
% 1.49/1.06  smt_fast_solver_time:                   0.
% 1.49/1.06  prop_fast_solver_time:                  0.
% 1.49/1.06  prop_unsat_core_time:                   0.
% 1.49/1.06  
% 1.49/1.06  ------ QBF
% 1.49/1.06  
% 1.49/1.06  qbf_q_res:                              0
% 1.49/1.06  qbf_num_tautologies:                    0
% 1.49/1.06  qbf_prep_cycles:                        0
% 1.49/1.06  
% 1.49/1.06  ------ BMC1
% 1.49/1.06  
% 1.49/1.06  bmc1_current_bound:                     -1
% 1.49/1.06  bmc1_last_solved_bound:                 -1
% 1.49/1.06  bmc1_unsat_core_size:                   -1
% 1.49/1.06  bmc1_unsat_core_parents_size:           -1
% 1.49/1.06  bmc1_merge_next_fun:                    0
% 1.49/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.49/1.06  
% 1.49/1.06  ------ Instantiation
% 1.49/1.06  
% 1.49/1.06  inst_num_of_clauses:                    379
% 1.49/1.06  inst_num_in_passive:                    58
% 1.49/1.06  inst_num_in_active:                     213
% 1.49/1.06  inst_num_in_unprocessed:                108
% 1.49/1.06  inst_num_of_loops:                      240
% 1.49/1.06  inst_num_of_learning_restarts:          0
% 1.49/1.06  inst_num_moves_active_passive:          23
% 1.49/1.06  inst_lit_activity:                      0
% 1.49/1.06  inst_lit_activity_moves:                0
% 1.49/1.06  inst_num_tautologies:                   0
% 1.49/1.06  inst_num_prop_implied:                  0
% 1.49/1.06  inst_num_existing_simplified:           0
% 1.49/1.06  inst_num_eq_res_simplified:             0
% 1.49/1.06  inst_num_child_elim:                    0
% 1.49/1.06  inst_num_of_dismatching_blockings:      108
% 1.49/1.06  inst_num_of_non_proper_insts:           488
% 1.49/1.06  inst_num_of_duplicates:                 0
% 1.49/1.06  inst_inst_num_from_inst_to_res:         0
% 1.49/1.06  inst_dismatching_checking_time:         0.
% 1.49/1.06  
% 1.49/1.06  ------ Resolution
% 1.49/1.06  
% 1.49/1.06  res_num_of_clauses:                     0
% 1.49/1.06  res_num_in_passive:                     0
% 1.49/1.06  res_num_in_active:                      0
% 1.49/1.06  res_num_of_loops:                       136
% 1.49/1.06  res_forward_subset_subsumed:            48
% 1.49/1.06  res_backward_subset_subsumed:           4
% 1.49/1.06  res_forward_subsumed:                   0
% 1.49/1.06  res_backward_subsumed:                  0
% 1.49/1.06  res_forward_subsumption_resolution:     0
% 1.49/1.06  res_backward_subsumption_resolution:    0
% 1.49/1.06  res_clause_to_clause_subsumption:       248
% 1.49/1.06  res_orphan_elimination:                 0
% 1.49/1.06  res_tautology_del:                      74
% 1.49/1.06  res_num_eq_res_simplified:              0
% 1.49/1.06  res_num_sel_changes:                    0
% 1.49/1.06  res_moves_from_active_to_pass:          0
% 1.49/1.06  
% 1.49/1.06  ------ Superposition
% 1.49/1.06  
% 1.49/1.06  sup_time_total:                         0.
% 1.49/1.06  sup_time_generating:                    0.
% 1.49/1.06  sup_time_sim_full:                      0.
% 1.49/1.06  sup_time_sim_immed:                     0.
% 1.49/1.06  
% 1.49/1.06  sup_num_of_clauses:                     61
% 1.49/1.06  sup_num_in_active:                      44
% 1.49/1.06  sup_num_in_passive:                     17
% 1.49/1.06  sup_num_of_loops:                       46
% 1.49/1.06  sup_fw_superposition:                   38
% 1.49/1.06  sup_bw_superposition:                   31
% 1.49/1.06  sup_immediate_simplified:               16
% 1.49/1.06  sup_given_eliminated:                   0
% 1.49/1.06  comparisons_done:                       0
% 1.49/1.06  comparisons_avoided:                    0
% 1.49/1.06  
% 1.49/1.06  ------ Simplifications
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  sim_fw_subset_subsumed:                 4
% 1.49/1.06  sim_bw_subset_subsumed:                 0
% 1.49/1.06  sim_fw_subsumed:                        9
% 1.49/1.06  sim_bw_subsumed:                        0
% 1.49/1.06  sim_fw_subsumption_res:                 0
% 1.49/1.06  sim_bw_subsumption_res:                 0
% 1.49/1.06  sim_tautology_del:                      3
% 1.49/1.06  sim_eq_tautology_del:                   6
% 1.49/1.06  sim_eq_res_simp:                        1
% 1.49/1.06  sim_fw_demodulated:                     1
% 1.49/1.06  sim_bw_demodulated:                     3
% 1.49/1.06  sim_light_normalised:                   6
% 1.49/1.06  sim_joinable_taut:                      0
% 1.49/1.06  sim_joinable_simp:                      0
% 1.49/1.06  sim_ac_normalised:                      0
% 1.49/1.06  sim_smt_subsumption:                    0
% 1.49/1.06  
%------------------------------------------------------------------------------
