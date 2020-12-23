%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:58 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 807 expanded)
%              Number of clauses        :   63 ( 191 expanded)
%              Number of leaves         :   21 ( 243 expanded)
%              Depth                    :   17
%              Number of atoms          :  237 (1075 expanded)
%              Number of equality atoms :  119 ( 734 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f50,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f57,f60,f60])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f64,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f74,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f60,f60,f60,f64])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f60])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f63,f63])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( v4_relat_1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_617,plain,
    ( v4_relat_1(k6_partfun1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_613,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_193,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ v1_relat_1(X0)
    | X1 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_194,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_612,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_925,plain,
    ( v4_relat_1(X0,sK1) != iProver_top
    | v4_relat_1(X0,sK0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_612])).

cnf(c_1244,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0) = iProver_top
    | v1_relat_1(k6_partfun1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_925])).

cnf(c_13,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_616,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1326,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1244,c_616])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_618,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1935,plain,
    ( k7_relat_1(k6_partfun1(sK1),sK0) = k6_partfun1(sK1)
    | v1_relat_1(k6_partfun1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1326,c_618])).

cnf(c_2063,plain,
    ( k7_relat_1(k6_partfun1(sK1),sK0) = k6_partfun1(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1935,c_616])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_620,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1913,plain,
    ( k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(superposition,[status(thm)],[c_616,c_620])).

cnf(c_2065,plain,
    ( k9_relat_1(k6_partfun1(sK1),sK0) = k2_relat_1(k6_partfun1(sK1)) ),
    inference(superposition,[status(thm)],[c_2063,c_1913])).

cnf(c_6,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2070,plain,
    ( k9_relat_1(k6_partfun1(sK1),sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_2065,c_6])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_619,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2663,plain,
    ( k10_relat_1(k6_partfun1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_partfun1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_619])).

cnf(c_10,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_181,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | k6_partfun1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_182,plain,
    ( ~ v2_funct_1(k6_partfun1(X0))
    | ~ v1_relat_1(k6_partfun1(X0))
    | k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_12,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_186,plain,
    ( k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_13,c_12])).

cnf(c_16,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_637,plain,
    ( k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_186,c_16])).

cnf(c_2681,plain,
    ( k1_relat_1(k5_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2663,c_637])).

cnf(c_4833,plain,
    ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k9_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) ),
    inference(superposition,[status(thm)],[c_616,c_2681])).

cnf(c_15,plain,
    ( k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1102,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) ),
    inference(superposition,[status(thm)],[c_15,c_6])).

cnf(c_7,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1101,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) ),
    inference(superposition,[status(thm)],[c_15,c_7])).

cnf(c_1444,plain,
    ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k2_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
    inference(demodulation,[status(thm)],[c_1102,c_1101])).

cnf(c_4860,plain,
    ( k9_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) = k2_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
    inference(light_normalisation,[status(thm)],[c_4833,c_1444])).

cnf(c_4861,plain,
    ( k2_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_4860,c_7])).

cnf(c_4885,plain,
    ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_4861,c_1444])).

cnf(c_1104,plain,
    ( k6_partfun1(k2_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)))) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) ),
    inference(demodulation,[status(thm)],[c_1102,c_15])).

cnf(c_4887,plain,
    ( k6_partfun1(k9_relat_1(k6_partfun1(X0),X1)) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) ),
    inference(demodulation,[status(thm)],[c_4861,c_1104])).

cnf(c_0,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1441,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
    inference(superposition,[status(thm)],[c_0,c_1101])).

cnf(c_1842,plain,
    ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k2_relat_1(k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_1441,c_1102])).

cnf(c_4889,plain,
    ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k9_relat_1(k6_partfun1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_4861,c_1842])).

cnf(c_4899,plain,
    ( k1_relat_1(k6_partfun1(k9_relat_1(k6_partfun1(X0),X1))) = k9_relat_1(k6_partfun1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_4887,c_4889])).

cnf(c_4907,plain,
    ( k9_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_4885,c_4887,c_4899])).

cnf(c_5041,plain,
    ( k9_relat_1(k6_partfun1(sK0),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2070,c_4907])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_614,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_615,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2504,plain,
    ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(superposition,[status(thm)],[c_614,c_615])).

cnf(c_2505,plain,
    ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2504,c_637])).

cnf(c_19,negated_conjecture,
    ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2697,plain,
    ( k9_relat_1(k6_partfun1(sK0),sK1) != sK1 ),
    inference(demodulation,[status(thm)],[c_2505,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5041,c_2697])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:27:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 2.74/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.98  
% 2.74/0.98  ------  iProver source info
% 2.74/0.98  
% 2.74/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.98  git: non_committed_changes: false
% 2.74/0.98  git: last_make_outside_of_git: false
% 2.74/0.98  
% 2.74/0.98  ------ 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options
% 2.74/0.98  
% 2.74/0.98  --out_options                           all
% 2.74/0.98  --tptp_safe_out                         true
% 2.74/0.98  --problem_path                          ""
% 2.74/0.98  --include_path                          ""
% 2.74/0.98  --clausifier                            res/vclausify_rel
% 2.74/0.98  --clausifier_options                    --mode clausify
% 2.74/0.98  --stdin                                 false
% 2.74/0.98  --stats_out                             all
% 2.74/0.98  
% 2.74/0.98  ------ General Options
% 2.74/0.98  
% 2.74/0.98  --fof                                   false
% 2.74/0.98  --time_out_real                         305.
% 2.74/0.98  --time_out_virtual                      -1.
% 2.74/0.98  --symbol_type_check                     false
% 2.74/0.98  --clausify_out                          false
% 2.74/0.98  --sig_cnt_out                           false
% 2.74/0.98  --trig_cnt_out                          false
% 2.74/0.98  --trig_cnt_out_tolerance                1.
% 2.74/0.98  --trig_cnt_out_sk_spl                   false
% 2.74/0.98  --abstr_cl_out                          false
% 2.74/0.98  
% 2.74/0.98  ------ Global Options
% 2.74/0.98  
% 2.74/0.98  --schedule                              default
% 2.74/0.98  --add_important_lit                     false
% 2.74/0.98  --prop_solver_per_cl                    1000
% 2.74/0.98  --min_unsat_core                        false
% 2.74/0.98  --soft_assumptions                      false
% 2.74/0.98  --soft_lemma_size                       3
% 2.74/0.98  --prop_impl_unit_size                   0
% 2.74/0.98  --prop_impl_unit                        []
% 2.74/0.98  --share_sel_clauses                     true
% 2.74/0.98  --reset_solvers                         false
% 2.74/0.98  --bc_imp_inh                            [conj_cone]
% 2.74/0.98  --conj_cone_tolerance                   3.
% 2.74/0.98  --extra_neg_conj                        none
% 2.74/0.98  --large_theory_mode                     true
% 2.74/0.98  --prolific_symb_bound                   200
% 2.74/0.98  --lt_threshold                          2000
% 2.74/0.98  --clause_weak_htbl                      true
% 2.74/0.98  --gc_record_bc_elim                     false
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing Options
% 2.74/0.98  
% 2.74/0.98  --preprocessing_flag                    true
% 2.74/0.98  --time_out_prep_mult                    0.1
% 2.74/0.98  --splitting_mode                        input
% 2.74/0.98  --splitting_grd                         true
% 2.74/0.98  --splitting_cvd                         false
% 2.74/0.98  --splitting_cvd_svl                     false
% 2.74/0.98  --splitting_nvd                         32
% 2.74/0.98  --sub_typing                            true
% 2.74/0.98  --prep_gs_sim                           true
% 2.74/0.98  --prep_unflatten                        true
% 2.74/0.98  --prep_res_sim                          true
% 2.74/0.98  --prep_upred                            true
% 2.74/0.98  --prep_sem_filter                       exhaustive
% 2.74/0.98  --prep_sem_filter_out                   false
% 2.74/0.98  --pred_elim                             true
% 2.74/0.98  --res_sim_input                         true
% 2.74/0.98  --eq_ax_congr_red                       true
% 2.74/0.98  --pure_diseq_elim                       true
% 2.74/0.98  --brand_transform                       false
% 2.74/0.98  --non_eq_to_eq                          false
% 2.74/0.98  --prep_def_merge                        true
% 2.74/0.98  --prep_def_merge_prop_impl              false
% 2.74/0.98  --prep_def_merge_mbd                    true
% 2.74/0.98  --prep_def_merge_tr_red                 false
% 2.74/0.98  --prep_def_merge_tr_cl                  false
% 2.74/0.98  --smt_preprocessing                     true
% 2.74/0.98  --smt_ac_axioms                         fast
% 2.74/0.98  --preprocessed_out                      false
% 2.74/0.98  --preprocessed_stats                    false
% 2.74/0.98  
% 2.74/0.98  ------ Abstraction refinement Options
% 2.74/0.98  
% 2.74/0.98  --abstr_ref                             []
% 2.74/0.98  --abstr_ref_prep                        false
% 2.74/0.98  --abstr_ref_until_sat                   false
% 2.74/0.98  --abstr_ref_sig_restrict                funpre
% 2.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.98  --abstr_ref_under                       []
% 2.74/0.98  
% 2.74/0.98  ------ SAT Options
% 2.74/0.98  
% 2.74/0.98  --sat_mode                              false
% 2.74/0.98  --sat_fm_restart_options                ""
% 2.74/0.98  --sat_gr_def                            false
% 2.74/0.98  --sat_epr_types                         true
% 2.74/0.98  --sat_non_cyclic_types                  false
% 2.74/0.98  --sat_finite_models                     false
% 2.74/0.98  --sat_fm_lemmas                         false
% 2.74/0.98  --sat_fm_prep                           false
% 2.74/0.98  --sat_fm_uc_incr                        true
% 2.74/0.98  --sat_out_model                         small
% 2.74/0.98  --sat_out_clauses                       false
% 2.74/0.98  
% 2.74/0.98  ------ QBF Options
% 2.74/0.98  
% 2.74/0.98  --qbf_mode                              false
% 2.74/0.98  --qbf_elim_univ                         false
% 2.74/0.98  --qbf_dom_inst                          none
% 2.74/0.98  --qbf_dom_pre_inst                      false
% 2.74/0.98  --qbf_sk_in                             false
% 2.74/0.98  --qbf_pred_elim                         true
% 2.74/0.98  --qbf_split                             512
% 2.74/0.98  
% 2.74/0.98  ------ BMC1 Options
% 2.74/0.98  
% 2.74/0.98  --bmc1_incremental                      false
% 2.74/0.98  --bmc1_axioms                           reachable_all
% 2.74/0.98  --bmc1_min_bound                        0
% 2.74/0.98  --bmc1_max_bound                        -1
% 2.74/0.98  --bmc1_max_bound_default                -1
% 2.74/0.98  --bmc1_symbol_reachability              true
% 2.74/0.98  --bmc1_property_lemmas                  false
% 2.74/0.98  --bmc1_k_induction                      false
% 2.74/0.98  --bmc1_non_equiv_states                 false
% 2.74/0.98  --bmc1_deadlock                         false
% 2.74/0.98  --bmc1_ucm                              false
% 2.74/0.98  --bmc1_add_unsat_core                   none
% 2.74/0.98  --bmc1_unsat_core_children              false
% 2.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.98  --bmc1_out_stat                         full
% 2.74/0.98  --bmc1_ground_init                      false
% 2.74/0.98  --bmc1_pre_inst_next_state              false
% 2.74/0.98  --bmc1_pre_inst_state                   false
% 2.74/0.98  --bmc1_pre_inst_reach_state             false
% 2.74/0.98  --bmc1_out_unsat_core                   false
% 2.74/0.98  --bmc1_aig_witness_out                  false
% 2.74/0.98  --bmc1_verbose                          false
% 2.74/0.98  --bmc1_dump_clauses_tptp                false
% 2.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.98  --bmc1_dump_file                        -
% 2.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.98  --bmc1_ucm_extend_mode                  1
% 2.74/0.98  --bmc1_ucm_init_mode                    2
% 2.74/0.98  --bmc1_ucm_cone_mode                    none
% 2.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.98  --bmc1_ucm_relax_model                  4
% 2.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.98  --bmc1_ucm_layered_model                none
% 2.74/0.98  --bmc1_ucm_max_lemma_size               10
% 2.74/0.98  
% 2.74/0.98  ------ AIG Options
% 2.74/0.98  
% 2.74/0.98  --aig_mode                              false
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation Options
% 2.74/0.98  
% 2.74/0.98  --instantiation_flag                    true
% 2.74/0.98  --inst_sos_flag                         false
% 2.74/0.98  --inst_sos_phase                        true
% 2.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel_side                     num_symb
% 2.74/0.98  --inst_solver_per_active                1400
% 2.74/0.98  --inst_solver_calls_frac                1.
% 2.74/0.98  --inst_passive_queue_type               priority_queues
% 2.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.98  --inst_passive_queues_freq              [25;2]
% 2.74/0.98  --inst_dismatching                      true
% 2.74/0.98  --inst_eager_unprocessed_to_passive     true
% 2.74/0.98  --inst_prop_sim_given                   true
% 2.74/0.98  --inst_prop_sim_new                     false
% 2.74/0.98  --inst_subs_new                         false
% 2.74/0.98  --inst_eq_res_simp                      false
% 2.74/0.98  --inst_subs_given                       false
% 2.74/0.98  --inst_orphan_elimination               true
% 2.74/0.98  --inst_learning_loop_flag               true
% 2.74/0.98  --inst_learning_start                   3000
% 2.74/0.98  --inst_learning_factor                  2
% 2.74/0.98  --inst_start_prop_sim_after_learn       3
% 2.74/0.98  --inst_sel_renew                        solver
% 2.74/0.98  --inst_lit_activity_flag                true
% 2.74/0.98  --inst_restr_to_given                   false
% 2.74/0.98  --inst_activity_threshold               500
% 2.74/0.98  --inst_out_proof                        true
% 2.74/0.98  
% 2.74/0.98  ------ Resolution Options
% 2.74/0.98  
% 2.74/0.98  --resolution_flag                       true
% 2.74/0.98  --res_lit_sel                           adaptive
% 2.74/0.98  --res_lit_sel_side                      none
% 2.74/0.98  --res_ordering                          kbo
% 2.74/0.98  --res_to_prop_solver                    active
% 2.74/0.98  --res_prop_simpl_new                    false
% 2.74/0.98  --res_prop_simpl_given                  true
% 2.74/0.98  --res_passive_queue_type                priority_queues
% 2.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.98  --res_passive_queues_freq               [15;5]
% 2.74/0.98  --res_forward_subs                      full
% 2.74/0.98  --res_backward_subs                     full
% 2.74/0.98  --res_forward_subs_resolution           true
% 2.74/0.98  --res_backward_subs_resolution          true
% 2.74/0.98  --res_orphan_elimination                true
% 2.74/0.98  --res_time_limit                        2.
% 2.74/0.98  --res_out_proof                         true
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Options
% 2.74/0.98  
% 2.74/0.98  --superposition_flag                    true
% 2.74/0.98  --sup_passive_queue_type                priority_queues
% 2.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.98  --demod_completeness_check              fast
% 2.74/0.98  --demod_use_ground                      true
% 2.74/0.98  --sup_to_prop_solver                    passive
% 2.74/0.98  --sup_prop_simpl_new                    true
% 2.74/0.98  --sup_prop_simpl_given                  true
% 2.74/0.98  --sup_fun_splitting                     false
% 2.74/0.98  --sup_smt_interval                      50000
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Simplification Setup
% 2.74/0.98  
% 2.74/0.98  --sup_indices_passive                   []
% 2.74/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_full_bw                           [BwDemod]
% 2.74/0.98  --sup_immed_triv                        [TrivRules]
% 2.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_immed_bw_main                     []
% 2.74/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  
% 2.74/0.98  ------ Combination Options
% 2.74/0.98  
% 2.74/0.98  --comb_res_mult                         3
% 2.74/0.98  --comb_sup_mult                         2
% 2.74/0.98  --comb_inst_mult                        10
% 2.74/0.98  
% 2.74/0.98  ------ Debug Options
% 2.74/0.98  
% 2.74/0.98  --dbg_backtrace                         false
% 2.74/0.98  --dbg_dump_prop_clauses                 false
% 2.74/0.98  --dbg_dump_prop_clauses_file            -
% 2.74/0.98  --dbg_out_stat                          false
% 2.74/0.98  ------ Parsing...
% 2.74/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.98  ------ Proving...
% 2.74/0.98  ------ Problem Properties 
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  clauses                                 16
% 2.74/0.98  conjectures                             2
% 2.74/0.98  EPR                                     0
% 2.74/0.98  Horn                                    16
% 2.74/0.98  unary                                   11
% 2.74/0.98  binary                                  2
% 2.74/0.98  lits                                    25
% 2.74/0.98  lits eq                                 11
% 2.74/0.98  fd_pure                                 0
% 2.74/0.98  fd_pseudo                               0
% 2.74/0.98  fd_cond                                 0
% 2.74/0.98  fd_pseudo_cond                          0
% 2.74/0.98  AC symbols                              0
% 2.74/0.98  
% 2.74/0.98  ------ Schedule dynamic 5 is on 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  ------ 
% 2.74/0.98  Current options:
% 2.74/0.98  ------ 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options
% 2.74/0.98  
% 2.74/0.98  --out_options                           all
% 2.74/0.98  --tptp_safe_out                         true
% 2.74/0.98  --problem_path                          ""
% 2.74/0.98  --include_path                          ""
% 2.74/0.98  --clausifier                            res/vclausify_rel
% 2.74/0.98  --clausifier_options                    --mode clausify
% 2.74/0.98  --stdin                                 false
% 2.74/0.98  --stats_out                             all
% 2.74/0.98  
% 2.74/0.98  ------ General Options
% 2.74/0.98  
% 2.74/0.98  --fof                                   false
% 2.74/0.98  --time_out_real                         305.
% 2.74/0.98  --time_out_virtual                      -1.
% 2.74/0.98  --symbol_type_check                     false
% 2.74/0.98  --clausify_out                          false
% 2.74/0.98  --sig_cnt_out                           false
% 2.74/0.98  --trig_cnt_out                          false
% 2.74/0.98  --trig_cnt_out_tolerance                1.
% 2.74/0.98  --trig_cnt_out_sk_spl                   false
% 2.74/0.98  --abstr_cl_out                          false
% 2.74/0.98  
% 2.74/0.98  ------ Global Options
% 2.74/0.98  
% 2.74/0.98  --schedule                              default
% 2.74/0.98  --add_important_lit                     false
% 2.74/0.98  --prop_solver_per_cl                    1000
% 2.74/0.98  --min_unsat_core                        false
% 2.74/0.98  --soft_assumptions                      false
% 2.74/0.98  --soft_lemma_size                       3
% 2.74/0.98  --prop_impl_unit_size                   0
% 2.74/0.98  --prop_impl_unit                        []
% 2.74/0.98  --share_sel_clauses                     true
% 2.74/0.98  --reset_solvers                         false
% 2.74/0.98  --bc_imp_inh                            [conj_cone]
% 2.74/0.98  --conj_cone_tolerance                   3.
% 2.74/0.98  --extra_neg_conj                        none
% 2.74/0.98  --large_theory_mode                     true
% 2.74/0.98  --prolific_symb_bound                   200
% 2.74/0.98  --lt_threshold                          2000
% 2.74/0.98  --clause_weak_htbl                      true
% 2.74/0.98  --gc_record_bc_elim                     false
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing Options
% 2.74/0.98  
% 2.74/0.98  --preprocessing_flag                    true
% 2.74/0.98  --time_out_prep_mult                    0.1
% 2.74/0.98  --splitting_mode                        input
% 2.74/0.98  --splitting_grd                         true
% 2.74/0.98  --splitting_cvd                         false
% 2.74/0.98  --splitting_cvd_svl                     false
% 2.74/0.98  --splitting_nvd                         32
% 2.74/0.98  --sub_typing                            true
% 2.74/0.98  --prep_gs_sim                           true
% 2.74/0.98  --prep_unflatten                        true
% 2.74/0.98  --prep_res_sim                          true
% 2.74/0.98  --prep_upred                            true
% 2.74/0.98  --prep_sem_filter                       exhaustive
% 2.74/0.98  --prep_sem_filter_out                   false
% 2.74/0.98  --pred_elim                             true
% 2.74/0.98  --res_sim_input                         true
% 2.74/0.98  --eq_ax_congr_red                       true
% 2.74/0.98  --pure_diseq_elim                       true
% 2.74/0.98  --brand_transform                       false
% 2.74/0.98  --non_eq_to_eq                          false
% 2.74/0.98  --prep_def_merge                        true
% 2.74/0.98  --prep_def_merge_prop_impl              false
% 2.74/0.98  --prep_def_merge_mbd                    true
% 2.74/0.98  --prep_def_merge_tr_red                 false
% 2.74/0.98  --prep_def_merge_tr_cl                  false
% 2.74/0.98  --smt_preprocessing                     true
% 2.74/0.98  --smt_ac_axioms                         fast
% 2.74/0.98  --preprocessed_out                      false
% 2.74/0.98  --preprocessed_stats                    false
% 2.74/0.98  
% 2.74/0.98  ------ Abstraction refinement Options
% 2.74/0.98  
% 2.74/0.98  --abstr_ref                             []
% 2.74/0.98  --abstr_ref_prep                        false
% 2.74/0.98  --abstr_ref_until_sat                   false
% 2.74/0.98  --abstr_ref_sig_restrict                funpre
% 2.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.98  --abstr_ref_under                       []
% 2.74/0.98  
% 2.74/0.98  ------ SAT Options
% 2.74/0.98  
% 2.74/0.98  --sat_mode                              false
% 2.74/0.98  --sat_fm_restart_options                ""
% 2.74/0.98  --sat_gr_def                            false
% 2.74/0.98  --sat_epr_types                         true
% 2.74/0.98  --sat_non_cyclic_types                  false
% 2.74/0.98  --sat_finite_models                     false
% 2.74/0.98  --sat_fm_lemmas                         false
% 2.74/0.98  --sat_fm_prep                           false
% 2.74/0.98  --sat_fm_uc_incr                        true
% 2.74/0.98  --sat_out_model                         small
% 2.74/0.98  --sat_out_clauses                       false
% 2.74/0.98  
% 2.74/0.98  ------ QBF Options
% 2.74/0.98  
% 2.74/0.98  --qbf_mode                              false
% 2.74/0.98  --qbf_elim_univ                         false
% 2.74/0.98  --qbf_dom_inst                          none
% 2.74/0.98  --qbf_dom_pre_inst                      false
% 2.74/0.98  --qbf_sk_in                             false
% 2.74/0.98  --qbf_pred_elim                         true
% 2.74/0.98  --qbf_split                             512
% 2.74/0.98  
% 2.74/0.98  ------ BMC1 Options
% 2.74/0.98  
% 2.74/0.98  --bmc1_incremental                      false
% 2.74/0.98  --bmc1_axioms                           reachable_all
% 2.74/0.98  --bmc1_min_bound                        0
% 2.74/0.98  --bmc1_max_bound                        -1
% 2.74/0.98  --bmc1_max_bound_default                -1
% 2.74/0.98  --bmc1_symbol_reachability              true
% 2.74/0.98  --bmc1_property_lemmas                  false
% 2.74/0.98  --bmc1_k_induction                      false
% 2.74/0.98  --bmc1_non_equiv_states                 false
% 2.74/0.98  --bmc1_deadlock                         false
% 2.74/0.98  --bmc1_ucm                              false
% 2.74/0.98  --bmc1_add_unsat_core                   none
% 2.74/0.98  --bmc1_unsat_core_children              false
% 2.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.98  --bmc1_out_stat                         full
% 2.74/0.98  --bmc1_ground_init                      false
% 2.74/0.98  --bmc1_pre_inst_next_state              false
% 2.74/0.98  --bmc1_pre_inst_state                   false
% 2.74/0.98  --bmc1_pre_inst_reach_state             false
% 2.74/0.98  --bmc1_out_unsat_core                   false
% 2.74/0.98  --bmc1_aig_witness_out                  false
% 2.74/0.98  --bmc1_verbose                          false
% 2.74/0.98  --bmc1_dump_clauses_tptp                false
% 2.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.98  --bmc1_dump_file                        -
% 2.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.98  --bmc1_ucm_extend_mode                  1
% 2.74/0.98  --bmc1_ucm_init_mode                    2
% 2.74/0.98  --bmc1_ucm_cone_mode                    none
% 2.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.98  --bmc1_ucm_relax_model                  4
% 2.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.98  --bmc1_ucm_layered_model                none
% 2.74/0.98  --bmc1_ucm_max_lemma_size               10
% 2.74/0.98  
% 2.74/0.98  ------ AIG Options
% 2.74/0.98  
% 2.74/0.98  --aig_mode                              false
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation Options
% 2.74/0.98  
% 2.74/0.98  --instantiation_flag                    true
% 2.74/0.98  --inst_sos_flag                         false
% 2.74/0.98  --inst_sos_phase                        true
% 2.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel_side                     none
% 2.74/0.98  --inst_solver_per_active                1400
% 2.74/0.98  --inst_solver_calls_frac                1.
% 2.74/0.98  --inst_passive_queue_type               priority_queues
% 2.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.98  --inst_passive_queues_freq              [25;2]
% 2.74/0.98  --inst_dismatching                      true
% 2.74/0.98  --inst_eager_unprocessed_to_passive     true
% 2.74/0.98  --inst_prop_sim_given                   true
% 2.74/0.98  --inst_prop_sim_new                     false
% 2.74/0.98  --inst_subs_new                         false
% 2.74/0.98  --inst_eq_res_simp                      false
% 2.74/0.98  --inst_subs_given                       false
% 2.74/0.98  --inst_orphan_elimination               true
% 2.74/0.98  --inst_learning_loop_flag               true
% 2.74/0.98  --inst_learning_start                   3000
% 2.74/0.98  --inst_learning_factor                  2
% 2.74/0.98  --inst_start_prop_sim_after_learn       3
% 2.74/0.98  --inst_sel_renew                        solver
% 2.74/0.98  --inst_lit_activity_flag                true
% 2.74/0.98  --inst_restr_to_given                   false
% 2.74/0.98  --inst_activity_threshold               500
% 2.74/0.98  --inst_out_proof                        true
% 2.74/0.98  
% 2.74/0.98  ------ Resolution Options
% 2.74/0.98  
% 2.74/0.98  --resolution_flag                       false
% 2.74/0.98  --res_lit_sel                           adaptive
% 2.74/0.98  --res_lit_sel_side                      none
% 2.74/0.98  --res_ordering                          kbo
% 2.74/0.98  --res_to_prop_solver                    active
% 2.74/0.98  --res_prop_simpl_new                    false
% 2.74/0.98  --res_prop_simpl_given                  true
% 2.74/0.98  --res_passive_queue_type                priority_queues
% 2.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.98  --res_passive_queues_freq               [15;5]
% 2.74/0.98  --res_forward_subs                      full
% 2.74/0.98  --res_backward_subs                     full
% 2.74/0.98  --res_forward_subs_resolution           true
% 2.74/0.98  --res_backward_subs_resolution          true
% 2.74/0.98  --res_orphan_elimination                true
% 2.74/0.98  --res_time_limit                        2.
% 2.74/0.98  --res_out_proof                         true
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Options
% 2.74/0.98  
% 2.74/0.98  --superposition_flag                    true
% 2.74/0.98  --sup_passive_queue_type                priority_queues
% 2.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.98  --demod_completeness_check              fast
% 2.74/0.98  --demod_use_ground                      true
% 2.74/0.98  --sup_to_prop_solver                    passive
% 2.74/0.98  --sup_prop_simpl_new                    true
% 2.74/0.98  --sup_prop_simpl_given                  true
% 2.74/0.98  --sup_fun_splitting                     false
% 2.74/0.98  --sup_smt_interval                      50000
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Simplification Setup
% 2.74/0.98  
% 2.74/0.98  --sup_indices_passive                   []
% 2.74/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_full_bw                           [BwDemod]
% 2.74/0.98  --sup_immed_triv                        [TrivRules]
% 2.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_immed_bw_main                     []
% 2.74/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  
% 2.74/0.98  ------ Combination Options
% 2.74/0.98  
% 2.74/0.98  --comb_res_mult                         3
% 2.74/0.98  --comb_sup_mult                         2
% 2.74/0.98  --comb_inst_mult                        10
% 2.74/0.98  
% 2.74/0.98  ------ Debug Options
% 2.74/0.98  
% 2.74/0.98  --dbg_backtrace                         false
% 2.74/0.98  --dbg_dump_prop_clauses                 false
% 2.74/0.98  --dbg_dump_prop_clauses_file            -
% 2.74/0.98  --dbg_out_stat                          false
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  ------ Proving...
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  % SZS status Theorem for theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  fof(f11,axiom,(
% 2.74/0.98    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f24,plain,(
% 2.74/0.98    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 2.74/0.98    inference(pure_predicate_removal,[],[f11])).
% 2.74/0.98  
% 2.74/0.98  fof(f50,plain,(
% 2.74/0.98    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f24])).
% 2.74/0.98  
% 2.74/0.98  fof(f19,axiom,(
% 2.74/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f60,plain,(
% 2.74/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f19])).
% 2.74/0.98  
% 2.74/0.98  fof(f68,plain,(
% 2.74/0.98    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 2.74/0.98    inference(definition_unfolding,[],[f50,f60])).
% 2.74/0.98  
% 2.74/0.98  fof(f20,conjecture,(
% 2.74/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f21,negated_conjecture,(
% 2.74/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 2.74/0.98    inference(negated_conjecture,[],[f20])).
% 2.74/0.98  
% 2.74/0.98  fof(f35,plain,(
% 2.74/0.98    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.98    inference(ennf_transformation,[],[f21])).
% 2.74/0.98  
% 2.74/0.98  fof(f36,plain,(
% 2.74/0.98    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.74/0.98    introduced(choice_axiom,[])).
% 2.74/0.98  
% 2.74/0.98  fof(f37,plain,(
% 2.74/0.98    k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.74/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).
% 2.74/0.98  
% 2.74/0.98  fof(f61,plain,(
% 2.74/0.98    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.74/0.98    inference(cnf_transformation,[],[f37])).
% 2.74/0.98  
% 2.74/0.98  fof(f5,axiom,(
% 2.74/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f22,plain,(
% 2.74/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.74/0.98    inference(unused_predicate_definition_removal,[],[f5])).
% 2.74/0.98  
% 2.74/0.98  fof(f25,plain,(
% 2.74/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.74/0.98    inference(ennf_transformation,[],[f22])).
% 2.74/0.98  
% 2.74/0.98  fof(f42,plain,(
% 2.74/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f25])).
% 2.74/0.98  
% 2.74/0.98  fof(f9,axiom,(
% 2.74/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f30,plain,(
% 2.74/0.98    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 2.74/0.98    inference(ennf_transformation,[],[f9])).
% 2.74/0.98  
% 2.74/0.98  fof(f31,plain,(
% 2.74/0.98    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 2.74/0.98    inference(flattening,[],[f30])).
% 2.74/0.98  
% 2.74/0.98  fof(f46,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f31])).
% 2.74/0.98  
% 2.74/0.98  fof(f13,axiom,(
% 2.74/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f53,plain,(
% 2.74/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f13])).
% 2.74/0.98  
% 2.74/0.98  fof(f73,plain,(
% 2.74/0.98    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.74/0.98    inference(definition_unfolding,[],[f53,f60])).
% 2.74/0.98  
% 2.74/0.98  fof(f8,axiom,(
% 2.74/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f28,plain,(
% 2.74/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.74/0.98    inference(ennf_transformation,[],[f8])).
% 2.74/0.98  
% 2.74/0.98  fof(f29,plain,(
% 2.74/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.74/0.98    inference(flattening,[],[f28])).
% 2.74/0.98  
% 2.74/0.98  fof(f45,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f29])).
% 2.74/0.98  
% 2.74/0.98  fof(f6,axiom,(
% 2.74/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f26,plain,(
% 2.74/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.74/0.98    inference(ennf_transformation,[],[f6])).
% 2.74/0.98  
% 2.74/0.98  fof(f43,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f26])).
% 2.74/0.98  
% 2.74/0.98  fof(f10,axiom,(
% 2.74/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f48,plain,(
% 2.74/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.74/0.98    inference(cnf_transformation,[],[f10])).
% 2.74/0.98  
% 2.74/0.98  fof(f66,plain,(
% 2.74/0.98    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.74/0.98    inference(definition_unfolding,[],[f48,f60])).
% 2.74/0.98  
% 2.74/0.98  fof(f7,axiom,(
% 2.74/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f27,plain,(
% 2.74/0.98    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.74/0.98    inference(ennf_transformation,[],[f7])).
% 2.74/0.98  
% 2.74/0.98  fof(f44,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f27])).
% 2.74/0.98  
% 2.74/0.98  fof(f12,axiom,(
% 2.74/0.98    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f52,plain,(
% 2.74/0.98    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f12])).
% 2.74/0.98  
% 2.74/0.98  fof(f70,plain,(
% 2.74/0.98    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 2.74/0.98    inference(definition_unfolding,[],[f52,f60])).
% 2.74/0.98  
% 2.74/0.98  fof(f14,axiom,(
% 2.74/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f32,plain,(
% 2.74/0.98    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.74/0.98    inference(ennf_transformation,[],[f14])).
% 2.74/0.98  
% 2.74/0.98  fof(f33,plain,(
% 2.74/0.98    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.74/0.98    inference(flattening,[],[f32])).
% 2.74/0.98  
% 2.74/0.98  fof(f55,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f33])).
% 2.74/0.98  
% 2.74/0.98  fof(f54,plain,(
% 2.74/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f13])).
% 2.74/0.98  
% 2.74/0.98  fof(f72,plain,(
% 2.74/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.74/0.98    inference(definition_unfolding,[],[f54,f60])).
% 2.74/0.98  
% 2.74/0.98  fof(f16,axiom,(
% 2.74/0.98    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f57,plain,(
% 2.74/0.98    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f16])).
% 2.74/0.98  
% 2.74/0.98  fof(f75,plain,(
% 2.74/0.98    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 2.74/0.98    inference(definition_unfolding,[],[f57,f60,f60])).
% 2.74/0.98  
% 2.74/0.98  fof(f15,axiom,(
% 2.74/0.98    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f56,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f15])).
% 2.74/0.98  
% 2.74/0.98  fof(f4,axiom,(
% 2.74/0.98    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f41,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f4])).
% 2.74/0.98  
% 2.74/0.98  fof(f2,axiom,(
% 2.74/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f39,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f2])).
% 2.74/0.98  
% 2.74/0.98  fof(f3,axiom,(
% 2.74/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f40,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f3])).
% 2.74/0.98  
% 2.74/0.98  fof(f63,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.74/0.98    inference(definition_unfolding,[],[f39,f40])).
% 2.74/0.98  
% 2.74/0.98  fof(f64,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.74/0.98    inference(definition_unfolding,[],[f41,f63])).
% 2.74/0.98  
% 2.74/0.98  fof(f74,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.74/0.98    inference(definition_unfolding,[],[f56,f60,f60,f60,f64])).
% 2.74/0.98  
% 2.74/0.98  fof(f47,plain,(
% 2.74/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.74/0.98    inference(cnf_transformation,[],[f10])).
% 2.74/0.98  
% 2.74/0.98  fof(f67,plain,(
% 2.74/0.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.74/0.98    inference(definition_unfolding,[],[f47,f60])).
% 2.74/0.98  
% 2.74/0.98  fof(f1,axiom,(
% 2.74/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f38,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f1])).
% 2.74/0.98  
% 2.74/0.98  fof(f65,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.74/0.98    inference(definition_unfolding,[],[f38,f63,f63])).
% 2.74/0.98  
% 2.74/0.98  fof(f18,axiom,(
% 2.74/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f23,plain,(
% 2.74/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.74/0.98    inference(pure_predicate_removal,[],[f18])).
% 2.74/0.98  
% 2.74/0.98  fof(f59,plain,(
% 2.74/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f23])).
% 2.74/0.98  
% 2.74/0.98  fof(f17,axiom,(
% 2.74/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f34,plain,(
% 2.74/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.98    inference(ennf_transformation,[],[f17])).
% 2.74/0.98  
% 2.74/0.98  fof(f58,plain,(
% 2.74/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f34])).
% 2.74/0.98  
% 2.74/0.98  fof(f62,plain,(
% 2.74/0.98    k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1),
% 2.74/0.98    inference(cnf_transformation,[],[f37])).
% 2.74/0.98  
% 2.74/0.98  cnf(c_8,plain,
% 2.74/0.98      ( v4_relat_1(k6_partfun1(X0),X0) ),
% 2.74/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_617,plain,
% 2.74/0.98      ( v4_relat_1(k6_partfun1(X0),X0) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_20,negated_conjecture,
% 2.74/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 2.74/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_613,plain,
% 2.74/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1,plain,
% 2.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_5,plain,
% 2.74/0.99      ( ~ v4_relat_1(X0,X1)
% 2.74/0.99      | v4_relat_1(X0,X2)
% 2.74/0.99      | ~ r1_tarski(X1,X2)
% 2.74/0.99      | ~ v1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_193,plain,
% 2.74/0.99      ( ~ v4_relat_1(X0,X1)
% 2.74/0.99      | v4_relat_1(X0,X2)
% 2.74/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | X1 != X3
% 2.74/0.99      | X2 != X4 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_194,plain,
% 2.74/0.99      ( ~ v4_relat_1(X0,X1)
% 2.74/0.99      | v4_relat_1(X0,X2)
% 2.74/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.74/0.99      | ~ v1_relat_1(X0) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_193]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_612,plain,
% 2.74/0.99      ( v4_relat_1(X0,X1) != iProver_top
% 2.74/0.99      | v4_relat_1(X0,X2) = iProver_top
% 2.74/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 2.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_925,plain,
% 2.74/0.99      ( v4_relat_1(X0,sK1) != iProver_top
% 2.74/0.99      | v4_relat_1(X0,sK0) = iProver_top
% 2.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_613,c_612]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1244,plain,
% 2.74/0.99      ( v4_relat_1(k6_partfun1(sK1),sK0) = iProver_top
% 2.74/0.99      | v1_relat_1(k6_partfun1(sK1)) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_617,c_925]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_13,plain,
% 2.74/0.99      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_616,plain,
% 2.74/0.99      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1326,plain,
% 2.74/0.99      ( v4_relat_1(k6_partfun1(sK1),sK0) = iProver_top ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1244,c_616]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4,plain,
% 2.74/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_618,plain,
% 2.74/0.99      ( k7_relat_1(X0,X1) = X0
% 2.74/0.99      | v4_relat_1(X0,X1) != iProver_top
% 2.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1935,plain,
% 2.74/0.99      ( k7_relat_1(k6_partfun1(sK1),sK0) = k6_partfun1(sK1)
% 2.74/0.99      | v1_relat_1(k6_partfun1(sK1)) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1326,c_618]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2063,plain,
% 2.74/0.99      ( k7_relat_1(k6_partfun1(sK1),sK0) = k6_partfun1(sK1) ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1935,c_616]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2,plain,
% 2.74/0.99      ( ~ v1_relat_1(X0)
% 2.74/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_620,plain,
% 2.74/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1913,plain,
% 2.74/0.99      ( k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_616,c_620]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2065,plain,
% 2.74/0.99      ( k9_relat_1(k6_partfun1(sK1),sK0) = k2_relat_1(k6_partfun1(sK1)) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2063,c_1913]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6,plain,
% 2.74/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2070,plain,
% 2.74/0.99      ( k9_relat_1(k6_partfun1(sK1),sK0) = sK1 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2065,c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3,plain,
% 2.74/0.99      ( ~ v1_relat_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_619,plain,
% 2.74/0.99      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.74/0.99      | v1_relat_1(X1) != iProver_top
% 2.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2663,plain,
% 2.74/0.99      ( k10_relat_1(k6_partfun1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_partfun1(X0),X1))
% 2.74/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_616,c_619]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_10,plain,
% 2.74/0.99      ( v1_funct_1(k6_partfun1(X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_14,plain,
% 2.74/0.99      ( ~ v2_funct_1(X0)
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_181,plain,
% 2.74/0.99      ( ~ v2_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 2.74/0.99      | k6_partfun1(X2) != X0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_182,plain,
% 2.74/0.99      ( ~ v2_funct_1(k6_partfun1(X0))
% 2.74/0.99      | ~ v1_relat_1(k6_partfun1(X0))
% 2.74/0.99      | k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_181]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_12,plain,
% 2.74/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_186,plain,
% 2.74/0.99      ( k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_182,c_13,c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_16,plain,
% 2.74/0.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_637,plain,
% 2.74/0.99      ( k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_186,c_16]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2681,plain,
% 2.74/0.99      ( k1_relat_1(k5_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),k1_relat_1(X1))
% 2.74/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2663,c_637]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4833,plain,
% 2.74/0.99      ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k9_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_616,c_2681]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_15,plain,
% 2.74/0.99      ( k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1102,plain,
% 2.74/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_15,c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7,plain,
% 2.74/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1101,plain,
% 2.74/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_15,c_7]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1444,plain,
% 2.74/0.99      ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k2_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_1102,c_1101]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4860,plain,
% 2.74/0.99      ( k9_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) = k2_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_4833,c_1444]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4861,plain,
% 2.74/0.99      ( k2_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4860,c_7]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4885,plain,
% 2.74/0.99      ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4861,c_1444]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1104,plain,
% 2.74/0.99      ( k6_partfun1(k2_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)))) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_1102,c_15]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4887,plain,
% 2.74/0.99      ( k6_partfun1(k9_relat_1(k6_partfun1(X0),X1)) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4861,c_1104]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_0,plain,
% 2.74/0.99      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1441,plain,
% 2.74/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_0,c_1101]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1842,plain,
% 2.74/0.99      ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k2_relat_1(k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_1441,c_1102]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4889,plain,
% 2.74/0.99      ( k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k9_relat_1(k6_partfun1(X1),X0) ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4861,c_1842]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4899,plain,
% 2.74/0.99      ( k1_relat_1(k6_partfun1(k9_relat_1(k6_partfun1(X0),X1))) = k9_relat_1(k6_partfun1(X1),X0) ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4887,c_4889]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4907,plain,
% 2.74/0.99      ( k9_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X1),X0) ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_4885,c_4887,c_4899]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5041,plain,
% 2.74/0.99      ( k9_relat_1(k6_partfun1(sK0),sK1) = sK1 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2070,c_4907]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_18,plain,
% 2.74/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.74/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_614,plain,
% 2.74/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_17,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.74/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_615,plain,
% 2.74/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2504,plain,
% 2.74/0.99      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_614,c_615]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2505,plain,
% 2.74/0.99      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_2504,c_637]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_19,negated_conjecture,
% 2.74/0.99      ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
% 2.74/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2697,plain,
% 2.74/0.99      ( k9_relat_1(k6_partfun1(sK0),sK1) != sK1 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2505,c_19]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(contradiction,plain,
% 2.74/0.99      ( $false ),
% 2.74/0.99      inference(minisat,[status(thm)],[c_5041,c_2697]) ).
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  ------                               Statistics
% 2.74/0.99  
% 2.74/0.99  ------ General
% 2.74/0.99  
% 2.74/0.99  abstr_ref_over_cycles:                  0
% 2.74/0.99  abstr_ref_under_cycles:                 0
% 2.74/0.99  gc_basic_clause_elim:                   0
% 2.74/0.99  forced_gc_time:                         0
% 2.74/0.99  parsing_time:                           0.011
% 2.74/0.99  unif_index_cands_time:                  0.
% 2.74/0.99  unif_index_add_time:                    0.
% 2.74/0.99  orderings_time:                         0.
% 2.74/0.99  out_proof_time:                         0.008
% 2.74/0.99  total_time:                             0.178
% 2.74/0.99  num_of_symbols:                         52
% 2.74/0.99  num_of_terms:                           6053
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing
% 2.74/0.99  
% 2.74/0.99  num_of_splits:                          0
% 2.74/0.99  num_of_split_atoms:                     0
% 2.74/0.99  num_of_reused_defs:                     0
% 2.74/0.99  num_eq_ax_congr_red:                    33
% 2.74/0.99  num_of_sem_filtered_clauses:            1
% 2.74/0.99  num_of_subtypes:                        0
% 2.74/0.99  monotx_restored_types:                  0
% 2.74/0.99  sat_num_of_epr_types:                   0
% 2.74/0.99  sat_num_of_non_cyclic_types:            0
% 2.74/0.99  sat_guarded_non_collapsed_types:        0
% 2.74/0.99  num_pure_diseq_elim:                    0
% 2.74/0.99  simp_replaced_by:                       0
% 2.74/0.99  res_preprocessed:                       98
% 2.74/0.99  prep_upred:                             0
% 2.74/0.99  prep_unflattend:                        11
% 2.74/0.99  smt_new_axioms:                         0
% 2.74/0.99  pred_elim_cands:                        3
% 2.74/0.99  pred_elim:                              3
% 2.74/0.99  pred_elim_cl:                           3
% 2.74/0.99  pred_elim_cycles:                       5
% 2.74/0.99  merged_defs:                            0
% 2.74/0.99  merged_defs_ncl:                        0
% 2.74/0.99  bin_hyper_res:                          0
% 2.74/0.99  prep_cycles:                            4
% 2.74/0.99  pred_elim_time:                         0.004
% 2.74/0.99  splitting_time:                         0.
% 2.74/0.99  sem_filter_time:                        0.
% 2.74/0.99  monotx_time:                            0.
% 2.74/0.99  subtype_inf_time:                       0.
% 2.74/0.99  
% 2.74/0.99  ------ Problem properties
% 2.74/0.99  
% 2.74/0.99  clauses:                                16
% 2.74/0.99  conjectures:                            2
% 2.74/0.99  epr:                                    0
% 2.74/0.99  horn:                                   16
% 2.74/0.99  ground:                                 2
% 2.74/0.99  unary:                                  11
% 2.74/0.99  binary:                                 2
% 2.74/0.99  lits:                                   25
% 2.74/0.99  lits_eq:                                11
% 2.74/0.99  fd_pure:                                0
% 2.74/0.99  fd_pseudo:                              0
% 2.74/0.99  fd_cond:                                0
% 2.74/0.99  fd_pseudo_cond:                         0
% 2.74/0.99  ac_symbols:                             0
% 2.74/0.99  
% 2.74/0.99  ------ Propositional Solver
% 2.74/0.99  
% 2.74/0.99  prop_solver_calls:                      27
% 2.74/0.99  prop_fast_solver_calls:                 487
% 2.74/0.99  smt_solver_calls:                       0
% 2.74/0.99  smt_fast_solver_calls:                  0
% 2.74/0.99  prop_num_of_clauses:                    2281
% 2.74/0.99  prop_preprocess_simplified:             5527
% 2.74/0.99  prop_fo_subsumed:                       3
% 2.74/0.99  prop_solver_time:                       0.
% 2.74/0.99  smt_solver_time:                        0.
% 2.74/0.99  smt_fast_solver_time:                   0.
% 2.74/0.99  prop_fast_solver_time:                  0.
% 2.74/0.99  prop_unsat_core_time:                   0.
% 2.74/0.99  
% 2.74/0.99  ------ QBF
% 2.74/0.99  
% 2.74/0.99  qbf_q_res:                              0
% 2.74/0.99  qbf_num_tautologies:                    0
% 2.74/0.99  qbf_prep_cycles:                        0
% 2.74/0.99  
% 2.74/0.99  ------ BMC1
% 2.74/0.99  
% 2.74/0.99  bmc1_current_bound:                     -1
% 2.74/0.99  bmc1_last_solved_bound:                 -1
% 2.74/0.99  bmc1_unsat_core_size:                   -1
% 2.74/0.99  bmc1_unsat_core_parents_size:           -1
% 2.74/0.99  bmc1_merge_next_fun:                    0
% 2.74/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation
% 2.74/0.99  
% 2.74/0.99  inst_num_of_clauses:                    697
% 2.74/0.99  inst_num_in_passive:                    269
% 2.74/0.99  inst_num_in_active:                     287
% 2.74/0.99  inst_num_in_unprocessed:                141
% 2.74/0.99  inst_num_of_loops:                      290
% 2.74/0.99  inst_num_of_learning_restarts:          0
% 2.74/0.99  inst_num_moves_active_passive:          0
% 2.74/0.99  inst_lit_activity:                      0
% 2.74/0.99  inst_lit_activity_moves:                0
% 2.74/0.99  inst_num_tautologies:                   0
% 2.74/0.99  inst_num_prop_implied:                  0
% 2.74/0.99  inst_num_existing_simplified:           0
% 2.74/0.99  inst_num_eq_res_simplified:             0
% 2.74/0.99  inst_num_child_elim:                    0
% 2.74/0.99  inst_num_of_dismatching_blockings:      46
% 2.74/0.99  inst_num_of_non_proper_insts:           424
% 2.74/0.99  inst_num_of_duplicates:                 0
% 2.74/0.99  inst_inst_num_from_inst_to_res:         0
% 2.74/0.99  inst_dismatching_checking_time:         0.
% 2.74/0.99  
% 2.74/0.99  ------ Resolution
% 2.74/0.99  
% 2.74/0.99  res_num_of_clauses:                     0
% 2.74/0.99  res_num_in_passive:                     0
% 2.74/0.99  res_num_in_active:                      0
% 2.74/0.99  res_num_of_loops:                       102
% 2.74/0.99  res_forward_subset_subsumed:            52
% 2.74/0.99  res_backward_subset_subsumed:           0
% 2.74/0.99  res_forward_subsumed:                   0
% 2.74/0.99  res_backward_subsumed:                  0
% 2.74/0.99  res_forward_subsumption_resolution:     0
% 2.74/0.99  res_backward_subsumption_resolution:    0
% 2.74/0.99  res_clause_to_clause_subsumption:       367
% 2.74/0.99  res_orphan_elimination:                 0
% 2.74/0.99  res_tautology_del:                      53
% 2.74/0.99  res_num_eq_res_simplified:              0
% 2.74/0.99  res_num_sel_changes:                    0
% 2.74/0.99  res_moves_from_active_to_pass:          0
% 2.74/0.99  
% 2.74/0.99  ------ Superposition
% 2.74/0.99  
% 2.74/0.99  sup_time_total:                         0.
% 2.74/0.99  sup_time_generating:                    0.
% 2.74/0.99  sup_time_sim_full:                      0.
% 2.74/0.99  sup_time_sim_immed:                     0.
% 2.74/0.99  
% 2.74/0.99  sup_num_of_clauses:                     150
% 2.74/0.99  sup_num_in_active:                      45
% 2.74/0.99  sup_num_in_passive:                     105
% 2.74/0.99  sup_num_of_loops:                       56
% 2.74/0.99  sup_fw_superposition:                   225
% 2.74/0.99  sup_bw_superposition:                   104
% 2.74/0.99  sup_immediate_simplified:               104
% 2.74/0.99  sup_given_eliminated:                   1
% 2.74/0.99  comparisons_done:                       0
% 2.74/0.99  comparisons_avoided:                    0
% 2.74/0.99  
% 2.74/0.99  ------ Simplifications
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  sim_fw_subset_subsumed:                 1
% 2.74/0.99  sim_bw_subset_subsumed:                 0
% 2.74/0.99  sim_fw_subsumed:                        2
% 2.74/0.99  sim_bw_subsumed:                        0
% 2.74/0.99  sim_fw_subsumption_res:                 2
% 2.74/0.99  sim_bw_subsumption_res:                 0
% 2.74/0.99  sim_tautology_del:                      0
% 2.74/0.99  sim_eq_tautology_del:                   0
% 2.74/0.99  sim_eq_res_simp:                        0
% 2.74/0.99  sim_fw_demodulated:                     51
% 2.74/0.99  sim_bw_demodulated:                     18
% 2.74/0.99  sim_light_normalised:                   51
% 2.74/0.99  sim_joinable_taut:                      0
% 2.74/0.99  sim_joinable_simp:                      0
% 2.74/0.99  sim_ac_normalised:                      0
% 2.74/0.99  sim_smt_subsumption:                    0
% 2.74/0.99  
%------------------------------------------------------------------------------
