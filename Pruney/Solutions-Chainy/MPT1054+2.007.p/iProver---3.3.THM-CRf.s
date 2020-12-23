%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:59 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 322 expanded)
%              Number of clauses        :   58 (  83 expanded)
%              Number of leaves         :   21 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  231 ( 472 expanded)
%              Number of equality atoms :  106 ( 271 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f49,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f34,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f63,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f62])).

fof(f74,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f59,f63,f59,f59])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f62,f62])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f53,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f56,f59,f59])).

fof(f61,plain,(
    k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( v4_relat_1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_570,plain,
    ( v4_relat_1(k6_partfun1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_567,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_193,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ v1_relat_1(X0)
    | X1 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_194,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_9,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_214,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k6_partfun1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_9])).

cnf(c_215,plain,
    ( ~ v4_relat_1(k6_partfun1(X0),X1)
    | v4_relat_1(k6_partfun1(X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_566,plain,
    ( v4_relat_1(k6_partfun1(X0),X1) != iProver_top
    | v4_relat_1(k6_partfun1(X0),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_2517,plain,
    ( v4_relat_1(k6_partfun1(X0),sK1) != iProver_top
    | v4_relat_1(k6_partfun1(X0),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_566])).

cnf(c_2812,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_570,c_2517])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_233,plain,
    ( ~ v4_relat_1(X0,X1)
    | k7_relat_1(X0,X1) = X0
    | k6_partfun1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_234,plain,
    ( ~ v4_relat_1(k6_partfun1(X0),X1)
    | k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(X0) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_565,plain,
    ( k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(X0)
    | v4_relat_1(k6_partfun1(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_2834,plain,
    ( k7_relat_1(k6_partfun1(sK1),sK0) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_2812,c_565])).

cnf(c_15,plain,
    ( k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_227,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0)
    | k6_partfun1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_228,plain,
    ( k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) = k7_relat_1(k6_partfun1(X1),X0) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_594,plain,
    ( k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_15,c_228])).

cnf(c_6,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_879,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_594,c_6])).

cnf(c_0,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_880,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_594,c_5])).

cnf(c_895,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_partfun1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_880])).

cnf(c_902,plain,
    ( k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k2_relat_1(k7_relat_1(k6_partfun1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_879,c_895])).

cnf(c_886,plain,
    ( k6_partfun1(k2_relat_1(k7_relat_1(k6_partfun1(X0),X1))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_880,c_594])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_245,plain,
    ( k6_partfun1(X0) != X1
    | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_246,plain,
    ( k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_1126,plain,
    ( k6_partfun1(k9_relat_1(k6_partfun1(X0),X1)) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_886,c_246])).

cnf(c_1137,plain,
    ( k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1126,c_6])).

cnf(c_1265,plain,
    ( k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_902,c_1137])).

cnf(c_2947,plain,
    ( k9_relat_1(k6_partfun1(sK0),sK1) = k2_relat_1(k6_partfun1(sK1)) ),
    inference(superposition,[status(thm)],[c_2834,c_1265])).

cnf(c_2959,plain,
    ( k9_relat_1(k6_partfun1(sK0),sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_2947,c_5])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_568,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_569,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1820,plain,
    ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(superposition,[status(thm)],[c_568,c_569])).

cnf(c_10,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

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

cnf(c_13,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_186,plain,
    ( k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_13,c_12])).

cnf(c_16,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_589,plain,
    ( k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_186,c_16])).

cnf(c_1821,plain,
    ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1820,c_589])).

cnf(c_19,negated_conjecture,
    ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2350,plain,
    ( k9_relat_1(k6_partfun1(sK0),sK1) != sK1 ),
    inference(demodulation,[status(thm)],[c_1821,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2959,c_2350])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:12:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.66/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/0.97  
% 2.66/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/0.97  
% 2.66/0.97  ------  iProver source info
% 2.66/0.97  
% 2.66/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.66/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/0.97  git: non_committed_changes: false
% 2.66/0.97  git: last_make_outside_of_git: false
% 2.66/0.97  
% 2.66/0.97  ------ 
% 2.66/0.97  
% 2.66/0.97  ------ Input Options
% 2.66/0.97  
% 2.66/0.97  --out_options                           all
% 2.66/0.97  --tptp_safe_out                         true
% 2.66/0.97  --problem_path                          ""
% 2.66/0.97  --include_path                          ""
% 2.66/0.97  --clausifier                            res/vclausify_rel
% 2.66/0.97  --clausifier_options                    --mode clausify
% 2.66/0.97  --stdin                                 false
% 2.66/0.97  --stats_out                             all
% 2.66/0.97  
% 2.66/0.97  ------ General Options
% 2.66/0.97  
% 2.66/0.97  --fof                                   false
% 2.66/0.97  --time_out_real                         305.
% 2.66/0.97  --time_out_virtual                      -1.
% 2.66/0.97  --symbol_type_check                     false
% 2.66/0.97  --clausify_out                          false
% 2.66/0.97  --sig_cnt_out                           false
% 2.66/0.97  --trig_cnt_out                          false
% 2.66/0.97  --trig_cnt_out_tolerance                1.
% 2.66/0.97  --trig_cnt_out_sk_spl                   false
% 2.66/0.97  --abstr_cl_out                          false
% 2.66/0.97  
% 2.66/0.97  ------ Global Options
% 2.66/0.97  
% 2.66/0.97  --schedule                              default
% 2.66/0.97  --add_important_lit                     false
% 2.66/0.97  --prop_solver_per_cl                    1000
% 2.66/0.97  --min_unsat_core                        false
% 2.66/0.97  --soft_assumptions                      false
% 2.66/0.97  --soft_lemma_size                       3
% 2.66/0.97  --prop_impl_unit_size                   0
% 2.66/0.97  --prop_impl_unit                        []
% 2.66/0.97  --share_sel_clauses                     true
% 2.66/0.97  --reset_solvers                         false
% 2.66/0.97  --bc_imp_inh                            [conj_cone]
% 2.66/0.97  --conj_cone_tolerance                   3.
% 2.66/0.97  --extra_neg_conj                        none
% 2.66/0.97  --large_theory_mode                     true
% 2.66/0.97  --prolific_symb_bound                   200
% 2.66/0.97  --lt_threshold                          2000
% 2.66/0.97  --clause_weak_htbl                      true
% 2.66/0.97  --gc_record_bc_elim                     false
% 2.66/0.97  
% 2.66/0.97  ------ Preprocessing Options
% 2.66/0.97  
% 2.66/0.97  --preprocessing_flag                    true
% 2.66/0.97  --time_out_prep_mult                    0.1
% 2.66/0.97  --splitting_mode                        input
% 2.66/0.97  --splitting_grd                         true
% 2.66/0.97  --splitting_cvd                         false
% 2.66/0.97  --splitting_cvd_svl                     false
% 2.66/0.97  --splitting_nvd                         32
% 2.66/0.97  --sub_typing                            true
% 2.66/0.97  --prep_gs_sim                           true
% 2.66/0.97  --prep_unflatten                        true
% 2.66/0.97  --prep_res_sim                          true
% 2.66/0.97  --prep_upred                            true
% 2.66/0.97  --prep_sem_filter                       exhaustive
% 2.66/0.97  --prep_sem_filter_out                   false
% 2.66/0.97  --pred_elim                             true
% 2.66/0.97  --res_sim_input                         true
% 2.66/0.97  --eq_ax_congr_red                       true
% 2.66/0.97  --pure_diseq_elim                       true
% 2.66/0.97  --brand_transform                       false
% 2.66/0.97  --non_eq_to_eq                          false
% 2.66/0.97  --prep_def_merge                        true
% 2.66/0.97  --prep_def_merge_prop_impl              false
% 2.66/0.97  --prep_def_merge_mbd                    true
% 2.66/0.97  --prep_def_merge_tr_red                 false
% 2.66/0.97  --prep_def_merge_tr_cl                  false
% 2.66/0.97  --smt_preprocessing                     true
% 2.66/0.97  --smt_ac_axioms                         fast
% 2.66/0.97  --preprocessed_out                      false
% 2.66/0.97  --preprocessed_stats                    false
% 2.66/0.97  
% 2.66/0.97  ------ Abstraction refinement Options
% 2.66/0.97  
% 2.66/0.97  --abstr_ref                             []
% 2.66/0.97  --abstr_ref_prep                        false
% 2.66/0.97  --abstr_ref_until_sat                   false
% 2.66/0.97  --abstr_ref_sig_restrict                funpre
% 2.66/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/0.97  --abstr_ref_under                       []
% 2.66/0.97  
% 2.66/0.97  ------ SAT Options
% 2.66/0.97  
% 2.66/0.97  --sat_mode                              false
% 2.66/0.97  --sat_fm_restart_options                ""
% 2.66/0.97  --sat_gr_def                            false
% 2.66/0.97  --sat_epr_types                         true
% 2.66/0.97  --sat_non_cyclic_types                  false
% 2.66/0.97  --sat_finite_models                     false
% 2.66/0.97  --sat_fm_lemmas                         false
% 2.66/0.97  --sat_fm_prep                           false
% 2.66/0.97  --sat_fm_uc_incr                        true
% 2.66/0.97  --sat_out_model                         small
% 2.66/0.97  --sat_out_clauses                       false
% 2.66/0.97  
% 2.66/0.97  ------ QBF Options
% 2.66/0.97  
% 2.66/0.97  --qbf_mode                              false
% 2.66/0.97  --qbf_elim_univ                         false
% 2.66/0.97  --qbf_dom_inst                          none
% 2.66/0.97  --qbf_dom_pre_inst                      false
% 2.66/0.97  --qbf_sk_in                             false
% 2.66/0.97  --qbf_pred_elim                         true
% 2.66/0.97  --qbf_split                             512
% 2.66/0.97  
% 2.66/0.97  ------ BMC1 Options
% 2.66/0.97  
% 2.66/0.97  --bmc1_incremental                      false
% 2.66/0.97  --bmc1_axioms                           reachable_all
% 2.66/0.97  --bmc1_min_bound                        0
% 2.66/0.97  --bmc1_max_bound                        -1
% 2.66/0.97  --bmc1_max_bound_default                -1
% 2.66/0.97  --bmc1_symbol_reachability              true
% 2.66/0.97  --bmc1_property_lemmas                  false
% 2.66/0.97  --bmc1_k_induction                      false
% 2.66/0.97  --bmc1_non_equiv_states                 false
% 2.66/0.97  --bmc1_deadlock                         false
% 2.66/0.97  --bmc1_ucm                              false
% 2.66/0.97  --bmc1_add_unsat_core                   none
% 2.66/0.97  --bmc1_unsat_core_children              false
% 2.66/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/0.97  --bmc1_out_stat                         full
% 2.66/0.97  --bmc1_ground_init                      false
% 2.66/0.97  --bmc1_pre_inst_next_state              false
% 2.66/0.97  --bmc1_pre_inst_state                   false
% 2.66/0.97  --bmc1_pre_inst_reach_state             false
% 2.66/0.97  --bmc1_out_unsat_core                   false
% 2.66/0.97  --bmc1_aig_witness_out                  false
% 2.66/0.97  --bmc1_verbose                          false
% 2.66/0.97  --bmc1_dump_clauses_tptp                false
% 2.66/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.66/0.97  --bmc1_dump_file                        -
% 2.66/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.66/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.66/0.97  --bmc1_ucm_extend_mode                  1
% 2.66/0.97  --bmc1_ucm_init_mode                    2
% 2.66/0.97  --bmc1_ucm_cone_mode                    none
% 2.66/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.66/0.97  --bmc1_ucm_relax_model                  4
% 2.66/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.66/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/0.97  --bmc1_ucm_layered_model                none
% 2.66/0.97  --bmc1_ucm_max_lemma_size               10
% 2.66/0.97  
% 2.66/0.97  ------ AIG Options
% 2.66/0.97  
% 2.66/0.97  --aig_mode                              false
% 2.66/0.97  
% 2.66/0.97  ------ Instantiation Options
% 2.66/0.97  
% 2.66/0.97  --instantiation_flag                    true
% 2.66/0.97  --inst_sos_flag                         false
% 2.66/0.97  --inst_sos_phase                        true
% 2.66/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/0.97  --inst_lit_sel_side                     num_symb
% 2.66/0.97  --inst_solver_per_active                1400
% 2.66/0.97  --inst_solver_calls_frac                1.
% 2.66/0.97  --inst_passive_queue_type               priority_queues
% 2.66/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/0.97  --inst_passive_queues_freq              [25;2]
% 2.66/0.97  --inst_dismatching                      true
% 2.66/0.97  --inst_eager_unprocessed_to_passive     true
% 2.66/0.97  --inst_prop_sim_given                   true
% 2.66/0.97  --inst_prop_sim_new                     false
% 2.66/0.97  --inst_subs_new                         false
% 2.66/0.97  --inst_eq_res_simp                      false
% 2.66/0.97  --inst_subs_given                       false
% 2.66/0.97  --inst_orphan_elimination               true
% 2.66/0.97  --inst_learning_loop_flag               true
% 2.66/0.97  --inst_learning_start                   3000
% 2.66/0.97  --inst_learning_factor                  2
% 2.66/0.97  --inst_start_prop_sim_after_learn       3
% 2.66/0.97  --inst_sel_renew                        solver
% 2.66/0.97  --inst_lit_activity_flag                true
% 2.66/0.97  --inst_restr_to_given                   false
% 2.66/0.97  --inst_activity_threshold               500
% 2.66/0.97  --inst_out_proof                        true
% 2.66/0.97  
% 2.66/0.97  ------ Resolution Options
% 2.66/0.97  
% 2.66/0.97  --resolution_flag                       true
% 2.66/0.97  --res_lit_sel                           adaptive
% 2.66/0.97  --res_lit_sel_side                      none
% 2.66/0.97  --res_ordering                          kbo
% 2.66/0.97  --res_to_prop_solver                    active
% 2.66/0.97  --res_prop_simpl_new                    false
% 2.66/0.97  --res_prop_simpl_given                  true
% 2.66/0.97  --res_passive_queue_type                priority_queues
% 2.66/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/0.97  --res_passive_queues_freq               [15;5]
% 2.66/0.97  --res_forward_subs                      full
% 2.66/0.97  --res_backward_subs                     full
% 2.66/0.97  --res_forward_subs_resolution           true
% 2.66/0.97  --res_backward_subs_resolution          true
% 2.66/0.97  --res_orphan_elimination                true
% 2.66/0.97  --res_time_limit                        2.
% 2.66/0.97  --res_out_proof                         true
% 2.66/0.97  
% 2.66/0.97  ------ Superposition Options
% 2.66/0.97  
% 2.66/0.97  --superposition_flag                    true
% 2.66/0.97  --sup_passive_queue_type                priority_queues
% 2.66/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.66/0.97  --demod_completeness_check              fast
% 2.66/0.97  --demod_use_ground                      true
% 2.66/0.97  --sup_to_prop_solver                    passive
% 2.66/0.97  --sup_prop_simpl_new                    true
% 2.66/0.97  --sup_prop_simpl_given                  true
% 2.66/0.97  --sup_fun_splitting                     false
% 2.66/0.97  --sup_smt_interval                      50000
% 2.66/0.97  
% 2.66/0.97  ------ Superposition Simplification Setup
% 2.66/0.97  
% 2.66/0.97  --sup_indices_passive                   []
% 2.66/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.97  --sup_full_bw                           [BwDemod]
% 2.66/0.97  --sup_immed_triv                        [TrivRules]
% 2.66/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.97  --sup_immed_bw_main                     []
% 2.66/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.97  
% 2.66/0.97  ------ Combination Options
% 2.66/0.97  
% 2.66/0.97  --comb_res_mult                         3
% 2.66/0.97  --comb_sup_mult                         2
% 2.66/0.97  --comb_inst_mult                        10
% 2.66/0.97  
% 2.66/0.97  ------ Debug Options
% 2.66/0.97  
% 2.66/0.97  --dbg_backtrace                         false
% 2.66/0.97  --dbg_dump_prop_clauses                 false
% 2.66/0.97  --dbg_dump_prop_clauses_file            -
% 2.66/0.97  --dbg_out_stat                          false
% 2.66/0.97  ------ Parsing...
% 2.66/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/0.97  
% 2.66/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.66/0.97  
% 2.66/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/0.97  
% 2.66/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/0.97  ------ Proving...
% 2.66/0.97  ------ Problem Properties 
% 2.66/0.97  
% 2.66/0.97  
% 2.66/0.97  clauses                                 15
% 2.66/0.97  conjectures                             2
% 2.66/0.97  EPR                                     0
% 2.66/0.97  Horn                                    15
% 2.66/0.97  unary                                   12
% 2.66/0.97  binary                                  2
% 2.66/0.97  lits                                    19
% 2.66/0.97  lits eq                                 11
% 2.66/0.97  fd_pure                                 0
% 2.66/0.97  fd_pseudo                               0
% 2.66/0.97  fd_cond                                 0
% 2.66/0.97  fd_pseudo_cond                          0
% 2.66/0.97  AC symbols                              0
% 2.66/0.97  
% 2.66/0.97  ------ Schedule dynamic 5 is on 
% 2.66/0.97  
% 2.66/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/0.97  
% 2.66/0.97  
% 2.66/0.97  ------ 
% 2.66/0.97  Current options:
% 2.66/0.97  ------ 
% 2.66/0.97  
% 2.66/0.97  ------ Input Options
% 2.66/0.97  
% 2.66/0.97  --out_options                           all
% 2.66/0.97  --tptp_safe_out                         true
% 2.66/0.97  --problem_path                          ""
% 2.66/0.97  --include_path                          ""
% 2.66/0.97  --clausifier                            res/vclausify_rel
% 2.66/0.97  --clausifier_options                    --mode clausify
% 2.66/0.97  --stdin                                 false
% 2.66/0.97  --stats_out                             all
% 2.66/0.97  
% 2.66/0.97  ------ General Options
% 2.66/0.97  
% 2.66/0.97  --fof                                   false
% 2.66/0.97  --time_out_real                         305.
% 2.66/0.97  --time_out_virtual                      -1.
% 2.66/0.97  --symbol_type_check                     false
% 2.66/0.97  --clausify_out                          false
% 2.66/0.97  --sig_cnt_out                           false
% 2.66/0.97  --trig_cnt_out                          false
% 2.66/0.97  --trig_cnt_out_tolerance                1.
% 2.66/0.97  --trig_cnt_out_sk_spl                   false
% 2.66/0.97  --abstr_cl_out                          false
% 2.66/0.97  
% 2.66/0.97  ------ Global Options
% 2.66/0.97  
% 2.66/0.97  --schedule                              default
% 2.66/0.97  --add_important_lit                     false
% 2.66/0.97  --prop_solver_per_cl                    1000
% 2.66/0.97  --min_unsat_core                        false
% 2.66/0.97  --soft_assumptions                      false
% 2.66/0.97  --soft_lemma_size                       3
% 2.66/0.97  --prop_impl_unit_size                   0
% 2.66/0.97  --prop_impl_unit                        []
% 2.66/0.97  --share_sel_clauses                     true
% 2.66/0.97  --reset_solvers                         false
% 2.66/0.97  --bc_imp_inh                            [conj_cone]
% 2.66/0.97  --conj_cone_tolerance                   3.
% 2.66/0.97  --extra_neg_conj                        none
% 2.66/0.97  --large_theory_mode                     true
% 2.66/0.97  --prolific_symb_bound                   200
% 2.66/0.97  --lt_threshold                          2000
% 2.66/0.97  --clause_weak_htbl                      true
% 2.66/0.97  --gc_record_bc_elim                     false
% 2.66/0.97  
% 2.66/0.97  ------ Preprocessing Options
% 2.66/0.97  
% 2.66/0.97  --preprocessing_flag                    true
% 2.66/0.97  --time_out_prep_mult                    0.1
% 2.66/0.97  --splitting_mode                        input
% 2.66/0.97  --splitting_grd                         true
% 2.66/0.97  --splitting_cvd                         false
% 2.66/0.97  --splitting_cvd_svl                     false
% 2.66/0.97  --splitting_nvd                         32
% 2.66/0.97  --sub_typing                            true
% 2.66/0.97  --prep_gs_sim                           true
% 2.66/0.97  --prep_unflatten                        true
% 2.66/0.97  --prep_res_sim                          true
% 2.66/0.97  --prep_upred                            true
% 2.66/0.97  --prep_sem_filter                       exhaustive
% 2.66/0.97  --prep_sem_filter_out                   false
% 2.66/0.97  --pred_elim                             true
% 2.66/0.97  --res_sim_input                         true
% 2.66/0.97  --eq_ax_congr_red                       true
% 2.66/0.97  --pure_diseq_elim                       true
% 2.66/0.97  --brand_transform                       false
% 2.66/0.97  --non_eq_to_eq                          false
% 2.66/0.97  --prep_def_merge                        true
% 2.66/0.97  --prep_def_merge_prop_impl              false
% 2.66/0.97  --prep_def_merge_mbd                    true
% 2.66/0.97  --prep_def_merge_tr_red                 false
% 2.66/0.97  --prep_def_merge_tr_cl                  false
% 2.66/0.97  --smt_preprocessing                     true
% 2.66/0.97  --smt_ac_axioms                         fast
% 2.66/0.97  --preprocessed_out                      false
% 2.66/0.97  --preprocessed_stats                    false
% 2.66/0.97  
% 2.66/0.97  ------ Abstraction refinement Options
% 2.66/0.97  
% 2.66/0.97  --abstr_ref                             []
% 2.66/0.97  --abstr_ref_prep                        false
% 2.66/0.97  --abstr_ref_until_sat                   false
% 2.66/0.97  --abstr_ref_sig_restrict                funpre
% 2.66/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/0.97  --abstr_ref_under                       []
% 2.66/0.97  
% 2.66/0.97  ------ SAT Options
% 2.66/0.97  
% 2.66/0.97  --sat_mode                              false
% 2.66/0.97  --sat_fm_restart_options                ""
% 2.66/0.97  --sat_gr_def                            false
% 2.66/0.97  --sat_epr_types                         true
% 2.66/0.97  --sat_non_cyclic_types                  false
% 2.66/0.97  --sat_finite_models                     false
% 2.66/0.97  --sat_fm_lemmas                         false
% 2.66/0.97  --sat_fm_prep                           false
% 2.66/0.97  --sat_fm_uc_incr                        true
% 2.66/0.97  --sat_out_model                         small
% 2.66/0.97  --sat_out_clauses                       false
% 2.66/0.97  
% 2.66/0.97  ------ QBF Options
% 2.66/0.97  
% 2.66/0.97  --qbf_mode                              false
% 2.66/0.97  --qbf_elim_univ                         false
% 2.66/0.97  --qbf_dom_inst                          none
% 2.66/0.97  --qbf_dom_pre_inst                      false
% 2.66/0.97  --qbf_sk_in                             false
% 2.66/0.97  --qbf_pred_elim                         true
% 2.66/0.97  --qbf_split                             512
% 2.66/0.97  
% 2.66/0.97  ------ BMC1 Options
% 2.66/0.97  
% 2.66/0.97  --bmc1_incremental                      false
% 2.66/0.97  --bmc1_axioms                           reachable_all
% 2.66/0.97  --bmc1_min_bound                        0
% 2.66/0.97  --bmc1_max_bound                        -1
% 2.66/0.97  --bmc1_max_bound_default                -1
% 2.66/0.97  --bmc1_symbol_reachability              true
% 2.66/0.97  --bmc1_property_lemmas                  false
% 2.66/0.97  --bmc1_k_induction                      false
% 2.66/0.97  --bmc1_non_equiv_states                 false
% 2.66/0.97  --bmc1_deadlock                         false
% 2.66/0.97  --bmc1_ucm                              false
% 2.66/0.97  --bmc1_add_unsat_core                   none
% 2.66/0.97  --bmc1_unsat_core_children              false
% 2.66/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/0.97  --bmc1_out_stat                         full
% 2.66/0.97  --bmc1_ground_init                      false
% 2.66/0.97  --bmc1_pre_inst_next_state              false
% 2.66/0.97  --bmc1_pre_inst_state                   false
% 2.66/0.97  --bmc1_pre_inst_reach_state             false
% 2.66/0.97  --bmc1_out_unsat_core                   false
% 2.66/0.97  --bmc1_aig_witness_out                  false
% 2.66/0.97  --bmc1_verbose                          false
% 2.66/0.97  --bmc1_dump_clauses_tptp                false
% 2.66/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.66/0.97  --bmc1_dump_file                        -
% 2.66/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.66/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.66/0.97  --bmc1_ucm_extend_mode                  1
% 2.66/0.97  --bmc1_ucm_init_mode                    2
% 2.66/0.97  --bmc1_ucm_cone_mode                    none
% 2.66/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.66/0.97  --bmc1_ucm_relax_model                  4
% 2.66/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.66/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/0.97  --bmc1_ucm_layered_model                none
% 2.66/0.97  --bmc1_ucm_max_lemma_size               10
% 2.66/0.97  
% 2.66/0.97  ------ AIG Options
% 2.66/0.97  
% 2.66/0.97  --aig_mode                              false
% 2.66/0.97  
% 2.66/0.97  ------ Instantiation Options
% 2.66/0.97  
% 2.66/0.97  --instantiation_flag                    true
% 2.66/0.97  --inst_sos_flag                         false
% 2.66/0.97  --inst_sos_phase                        true
% 2.66/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/0.97  --inst_lit_sel_side                     none
% 2.66/0.97  --inst_solver_per_active                1400
% 2.66/0.97  --inst_solver_calls_frac                1.
% 2.66/0.97  --inst_passive_queue_type               priority_queues
% 2.66/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/0.97  --inst_passive_queues_freq              [25;2]
% 2.66/0.97  --inst_dismatching                      true
% 2.66/0.97  --inst_eager_unprocessed_to_passive     true
% 2.66/0.97  --inst_prop_sim_given                   true
% 2.66/0.97  --inst_prop_sim_new                     false
% 2.66/0.97  --inst_subs_new                         false
% 2.66/0.97  --inst_eq_res_simp                      false
% 2.66/0.97  --inst_subs_given                       false
% 2.66/0.97  --inst_orphan_elimination               true
% 2.66/0.97  --inst_learning_loop_flag               true
% 2.66/0.97  --inst_learning_start                   3000
% 2.66/0.97  --inst_learning_factor                  2
% 2.66/0.97  --inst_start_prop_sim_after_learn       3
% 2.66/0.97  --inst_sel_renew                        solver
% 2.66/0.97  --inst_lit_activity_flag                true
% 2.66/0.97  --inst_restr_to_given                   false
% 2.66/0.97  --inst_activity_threshold               500
% 2.66/0.97  --inst_out_proof                        true
% 2.66/0.97  
% 2.66/0.97  ------ Resolution Options
% 2.66/0.97  
% 2.66/0.97  --resolution_flag                       false
% 2.66/0.97  --res_lit_sel                           adaptive
% 2.66/0.97  --res_lit_sel_side                      none
% 2.66/0.97  --res_ordering                          kbo
% 2.66/0.97  --res_to_prop_solver                    active
% 2.66/0.97  --res_prop_simpl_new                    false
% 2.66/0.97  --res_prop_simpl_given                  true
% 2.66/0.97  --res_passive_queue_type                priority_queues
% 2.66/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/0.97  --res_passive_queues_freq               [15;5]
% 2.66/0.97  --res_forward_subs                      full
% 2.66/0.97  --res_backward_subs                     full
% 2.66/0.97  --res_forward_subs_resolution           true
% 2.66/0.97  --res_backward_subs_resolution          true
% 2.66/0.97  --res_orphan_elimination                true
% 2.66/0.97  --res_time_limit                        2.
% 2.66/0.97  --res_out_proof                         true
% 2.66/0.97  
% 2.66/0.97  ------ Superposition Options
% 2.66/0.97  
% 2.66/0.97  --superposition_flag                    true
% 2.66/0.97  --sup_passive_queue_type                priority_queues
% 2.66/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.66/0.97  --demod_completeness_check              fast
% 2.66/0.97  --demod_use_ground                      true
% 2.66/0.97  --sup_to_prop_solver                    passive
% 2.66/0.97  --sup_prop_simpl_new                    true
% 2.66/0.97  --sup_prop_simpl_given                  true
% 2.66/0.97  --sup_fun_splitting                     false
% 2.66/0.97  --sup_smt_interval                      50000
% 2.66/0.97  
% 2.66/0.97  ------ Superposition Simplification Setup
% 2.66/0.97  
% 2.66/0.97  --sup_indices_passive                   []
% 2.66/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.97  --sup_full_bw                           [BwDemod]
% 2.66/0.97  --sup_immed_triv                        [TrivRules]
% 2.66/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.98  --sup_immed_bw_main                     []
% 2.66/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.98  
% 2.66/0.98  ------ Combination Options
% 2.66/0.98  
% 2.66/0.98  --comb_res_mult                         3
% 2.66/0.98  --comb_sup_mult                         2
% 2.66/0.98  --comb_inst_mult                        10
% 2.66/0.98  
% 2.66/0.98  ------ Debug Options
% 2.66/0.98  
% 2.66/0.98  --dbg_backtrace                         false
% 2.66/0.98  --dbg_dump_prop_clauses                 false
% 2.66/0.98  --dbg_dump_prop_clauses_file            -
% 2.66/0.98  --dbg_out_stat                          false
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  ------ Proving...
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  % SZS status Theorem for theBenchmark.p
% 2.66/0.98  
% 2.66/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/0.98  
% 2.66/0.98  fof(f11,axiom,(
% 2.66/0.98    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f23,plain,(
% 2.66/0.98    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 2.66/0.98    inference(pure_predicate_removal,[],[f11])).
% 2.66/0.98  
% 2.66/0.98  fof(f49,plain,(
% 2.66/0.98    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f23])).
% 2.66/0.98  
% 2.66/0.98  fof(f19,axiom,(
% 2.66/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f59,plain,(
% 2.66/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f19])).
% 2.66/0.98  
% 2.66/0.98  fof(f68,plain,(
% 2.66/0.98    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 2.66/0.98    inference(definition_unfolding,[],[f49,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f20,conjecture,(
% 2.66/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f21,negated_conjecture,(
% 2.66/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 2.66/0.98    inference(negated_conjecture,[],[f20])).
% 2.66/0.98  
% 2.66/0.98  fof(f34,plain,(
% 2.66/0.98    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.98    inference(ennf_transformation,[],[f21])).
% 2.66/0.98  
% 2.66/0.98  fof(f35,plain,(
% 2.66/0.98    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.66/0.98    introduced(choice_axiom,[])).
% 2.66/0.98  
% 2.66/0.98  fof(f36,plain,(
% 2.66/0.98    k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).
% 2.66/0.98  
% 2.66/0.98  fof(f60,plain,(
% 2.66/0.98    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.66/0.98    inference(cnf_transformation,[],[f36])).
% 2.66/0.98  
% 2.66/0.98  fof(f5,axiom,(
% 2.66/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f22,plain,(
% 2.66/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.66/0.98    inference(unused_predicate_definition_removal,[],[f5])).
% 2.66/0.98  
% 2.66/0.98  fof(f24,plain,(
% 2.66/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.66/0.98    inference(ennf_transformation,[],[f22])).
% 2.66/0.98  
% 2.66/0.98  fof(f41,plain,(
% 2.66/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f24])).
% 2.66/0.98  
% 2.66/0.98  fof(f8,axiom,(
% 2.66/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f28,plain,(
% 2.66/0.98    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 2.66/0.98    inference(ennf_transformation,[],[f8])).
% 2.66/0.98  
% 2.66/0.98  fof(f29,plain,(
% 2.66/0.98    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 2.66/0.98    inference(flattening,[],[f28])).
% 2.66/0.98  
% 2.66/0.98  fof(f44,plain,(
% 2.66/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f29])).
% 2.66/0.98  
% 2.66/0.98  fof(f48,plain,(
% 2.66/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f23])).
% 2.66/0.98  
% 2.66/0.98  fof(f69,plain,(
% 2.66/0.98    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.66/0.98    inference(definition_unfolding,[],[f48,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f7,axiom,(
% 2.66/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f26,plain,(
% 2.66/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.66/0.98    inference(ennf_transformation,[],[f7])).
% 2.66/0.98  
% 2.66/0.98  fof(f27,plain,(
% 2.66/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.66/0.98    inference(flattening,[],[f26])).
% 2.66/0.98  
% 2.66/0.98  fof(f43,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f27])).
% 2.66/0.98  
% 2.66/0.98  fof(f15,axiom,(
% 2.66/0.98    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f55,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f15])).
% 2.66/0.98  
% 2.66/0.98  fof(f4,axiom,(
% 2.66/0.98    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f40,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f4])).
% 2.66/0.98  
% 2.66/0.98  fof(f2,axiom,(
% 2.66/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f38,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f2])).
% 2.66/0.98  
% 2.66/0.98  fof(f3,axiom,(
% 2.66/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f39,plain,(
% 2.66/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f3])).
% 2.66/0.98  
% 2.66/0.98  fof(f62,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.66/0.98    inference(definition_unfolding,[],[f38,f39])).
% 2.66/0.98  
% 2.66/0.98  fof(f63,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.66/0.98    inference(definition_unfolding,[],[f40,f62])).
% 2.66/0.98  
% 2.66/0.98  fof(f74,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.66/0.98    inference(definition_unfolding,[],[f55,f59,f63,f59,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f10,axiom,(
% 2.66/0.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f30,plain,(
% 2.66/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.66/0.98    inference(ennf_transformation,[],[f10])).
% 2.66/0.98  
% 2.66/0.98  fof(f47,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f30])).
% 2.66/0.98  
% 2.66/0.98  fof(f67,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.66/0.98    inference(definition_unfolding,[],[f47,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f9,axiom,(
% 2.66/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f45,plain,(
% 2.66/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.66/0.98    inference(cnf_transformation,[],[f9])).
% 2.66/0.98  
% 2.66/0.98  fof(f66,plain,(
% 2.66/0.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.66/0.98    inference(definition_unfolding,[],[f45,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f1,axiom,(
% 2.66/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f37,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f1])).
% 2.66/0.98  
% 2.66/0.98  fof(f64,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.66/0.98    inference(definition_unfolding,[],[f37,f62,f62])).
% 2.66/0.98  
% 2.66/0.98  fof(f46,plain,(
% 2.66/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.66/0.98    inference(cnf_transformation,[],[f9])).
% 2.66/0.98  
% 2.66/0.98  fof(f65,plain,(
% 2.66/0.98    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.66/0.98    inference(definition_unfolding,[],[f46,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f6,axiom,(
% 2.66/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f25,plain,(
% 2.66/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.66/0.98    inference(ennf_transformation,[],[f6])).
% 2.66/0.98  
% 2.66/0.98  fof(f42,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f25])).
% 2.66/0.98  
% 2.66/0.98  fof(f18,axiom,(
% 2.66/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f58,plain,(
% 2.66/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f18])).
% 2.66/0.98  
% 2.66/0.98  fof(f76,plain,(
% 2.66/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.66/0.98    inference(definition_unfolding,[],[f58,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f17,axiom,(
% 2.66/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f33,plain,(
% 2.66/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(ennf_transformation,[],[f17])).
% 2.66/0.98  
% 2.66/0.98  fof(f57,plain,(
% 2.66/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f33])).
% 2.66/0.98  
% 2.66/0.98  fof(f12,axiom,(
% 2.66/0.98    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f51,plain,(
% 2.66/0.98    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f12])).
% 2.66/0.98  
% 2.66/0.98  fof(f70,plain,(
% 2.66/0.98    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 2.66/0.98    inference(definition_unfolding,[],[f51,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f14,axiom,(
% 2.66/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f31,plain,(
% 2.66/0.98    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.66/0.98    inference(ennf_transformation,[],[f14])).
% 2.66/0.98  
% 2.66/0.98  fof(f32,plain,(
% 2.66/0.98    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.66/0.98    inference(flattening,[],[f31])).
% 2.66/0.98  
% 2.66/0.98  fof(f54,plain,(
% 2.66/0.98    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f32])).
% 2.66/0.98  
% 2.66/0.98  fof(f13,axiom,(
% 2.66/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f52,plain,(
% 2.66/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f13])).
% 2.66/0.98  
% 2.66/0.98  fof(f73,plain,(
% 2.66/0.98    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.66/0.98    inference(definition_unfolding,[],[f52,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f53,plain,(
% 2.66/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f13])).
% 2.66/0.98  
% 2.66/0.98  fof(f72,plain,(
% 2.66/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.66/0.98    inference(definition_unfolding,[],[f53,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f16,axiom,(
% 2.66/0.98    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f56,plain,(
% 2.66/0.98    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f16])).
% 2.66/0.98  
% 2.66/0.98  fof(f75,plain,(
% 2.66/0.98    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 2.66/0.98    inference(definition_unfolding,[],[f56,f59,f59])).
% 2.66/0.98  
% 2.66/0.98  fof(f61,plain,(
% 2.66/0.98    k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1),
% 2.66/0.98    inference(cnf_transformation,[],[f36])).
% 2.66/0.98  
% 2.66/0.98  cnf(c_8,plain,
% 2.66/0.98      ( v4_relat_1(k6_partfun1(X0),X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_570,plain,
% 2.66/0.98      ( v4_relat_1(k6_partfun1(X0),X0) = iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_20,negated_conjecture,
% 2.66/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 2.66/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_567,plain,
% 2.66/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1,plain,
% 2.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.66/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4,plain,
% 2.66/0.98      ( ~ v4_relat_1(X0,X1)
% 2.66/0.98      | v4_relat_1(X0,X2)
% 2.66/0.98      | ~ r1_tarski(X1,X2)
% 2.66/0.98      | ~ v1_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_193,plain,
% 2.66/0.98      ( ~ v4_relat_1(X0,X1)
% 2.66/0.98      | v4_relat_1(X0,X2)
% 2.66/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | X1 != X3
% 2.66/0.98      | X2 != X4 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_4]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_194,plain,
% 2.66/0.98      ( ~ v4_relat_1(X0,X1)
% 2.66/0.98      | v4_relat_1(X0,X2)
% 2.66/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.66/0.98      | ~ v1_relat_1(X0) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_193]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_9,plain,
% 2.66/0.98      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.66/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_214,plain,
% 2.66/0.98      ( ~ v4_relat_1(X0,X1)
% 2.66/0.98      | v4_relat_1(X0,X2)
% 2.66/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.66/0.98      | k6_partfun1(X3) != X0 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_194,c_9]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_215,plain,
% 2.66/0.98      ( ~ v4_relat_1(k6_partfun1(X0),X1)
% 2.66/0.98      | v4_relat_1(k6_partfun1(X0),X2)
% 2.66/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_214]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_566,plain,
% 2.66/0.98      ( v4_relat_1(k6_partfun1(X0),X1) != iProver_top
% 2.66/0.98      | v4_relat_1(k6_partfun1(X0),X2) = iProver_top
% 2.66/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_2517,plain,
% 2.66/0.98      ( v4_relat_1(k6_partfun1(X0),sK1) != iProver_top
% 2.66/0.98      | v4_relat_1(k6_partfun1(X0),sK0) = iProver_top ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_567,c_566]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_2812,plain,
% 2.66/0.98      ( v4_relat_1(k6_partfun1(sK1),sK0) = iProver_top ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_570,c_2517]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3,plain,
% 2.66/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.66/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_233,plain,
% 2.66/0.98      ( ~ v4_relat_1(X0,X1)
% 2.66/0.98      | k7_relat_1(X0,X1) = X0
% 2.66/0.98      | k6_partfun1(X2) != X0 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_9]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_234,plain,
% 2.66/0.98      ( ~ v4_relat_1(k6_partfun1(X0),X1)
% 2.66/0.98      | k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(X0) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_233]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_565,plain,
% 2.66/0.98      ( k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(X0)
% 2.66/0.98      | v4_relat_1(k6_partfun1(X0),X1) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_2834,plain,
% 2.66/0.98      ( k7_relat_1(k6_partfun1(sK1),sK0) = k6_partfun1(sK1) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_2812,c_565]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_15,plain,
% 2.66/0.98      ( k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ),
% 2.66/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_7,plain,
% 2.66/0.98      ( ~ v1_relat_1(X0)
% 2.66/0.98      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 2.66/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_227,plain,
% 2.66/0.98      ( k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0)
% 2.66/0.98      | k6_partfun1(X2) != X1 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_228,plain,
% 2.66/0.98      ( k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) = k7_relat_1(k6_partfun1(X1),X0) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_227]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_594,plain,
% 2.66/0.98      ( k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(demodulation,[status(thm)],[c_15,c_228]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_6,plain,
% 2.66/0.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.66/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_879,plain,
% 2.66/0.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_594,c_6]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_0,plain,
% 2.66/0.98      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5,plain,
% 2.66/0.98      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 2.66/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_880,plain,
% 2.66/0.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_594,c_5]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_895,plain,
% 2.66/0.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_partfun1(X1),X0)) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_0,c_880]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_902,plain,
% 2.66/0.98      ( k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k2_relat_1(k7_relat_1(k6_partfun1(X1),X0)) ),
% 2.66/0.98      inference(light_normalisation,[status(thm)],[c_879,c_895]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_886,plain,
% 2.66/0.98      ( k6_partfun1(k2_relat_1(k7_relat_1(k6_partfun1(X0),X1))) = k7_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(demodulation,[status(thm)],[c_880,c_594]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_2,plain,
% 2.66/0.98      ( ~ v1_relat_1(X0)
% 2.66/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.66/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_245,plain,
% 2.66/0.98      ( k6_partfun1(X0) != X1
% 2.66/0.98      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_246,plain,
% 2.66/0.98      ( k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_245]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1126,plain,
% 2.66/0.98      ( k6_partfun1(k9_relat_1(k6_partfun1(X0),X1)) = k7_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(light_normalisation,[status(thm)],[c_886,c_246]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1137,plain,
% 2.66/0.98      ( k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_1126,c_6]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1265,plain,
% 2.66/0.98      ( k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X1),X0) ),
% 2.66/0.98      inference(light_normalisation,[status(thm)],[c_902,c_1137]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_2947,plain,
% 2.66/0.98      ( k9_relat_1(k6_partfun1(sK0),sK1) = k2_relat_1(k6_partfun1(sK1)) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_2834,c_1265]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_2959,plain,
% 2.66/0.98      ( k9_relat_1(k6_partfun1(sK0),sK1) = sK1 ),
% 2.66/0.98      inference(demodulation,[status(thm)],[c_2947,c_5]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_18,plain,
% 2.66/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.66/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_568,plain,
% 2.66/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_17,plain,
% 2.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.66/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_569,plain,
% 2.66/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.66/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1820,plain,
% 2.66/0.98      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_568,c_569]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_10,plain,
% 2.66/0.98      ( v1_funct_1(k6_partfun1(X0)) ),
% 2.66/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_14,plain,
% 2.66/0.98      ( ~ v2_funct_1(X0)
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.66/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_181,plain,
% 2.66/0.98      ( ~ v2_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 2.66/0.98      | k6_partfun1(X2) != X0 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_182,plain,
% 2.66/0.98      ( ~ v2_funct_1(k6_partfun1(X0))
% 2.66/0.98      | ~ v1_relat_1(k6_partfun1(X0))
% 2.66/0.98      | k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_181]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_13,plain,
% 2.66/0.98      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.66/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_12,plain,
% 2.66/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.66/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_186,plain,
% 2.66/0.98      ( k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_182,c_13,c_12]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_16,plain,
% 2.66/0.98      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_589,plain,
% 2.66/0.98      ( k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(light_normalisation,[status(thm)],[c_186,c_16]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1821,plain,
% 2.66/0.98      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
% 2.66/0.98      inference(light_normalisation,[status(thm)],[c_1820,c_589]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_19,negated_conjecture,
% 2.66/0.98      ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
% 2.66/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_2350,plain,
% 2.66/0.98      ( k9_relat_1(k6_partfun1(sK0),sK1) != sK1 ),
% 2.66/0.98      inference(demodulation,[status(thm)],[c_1821,c_19]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(contradiction,plain,
% 2.66/0.98      ( $false ),
% 2.66/0.98      inference(minisat,[status(thm)],[c_2959,c_2350]) ).
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/0.98  
% 2.66/0.98  ------                               Statistics
% 2.66/0.98  
% 2.66/0.98  ------ General
% 2.66/0.98  
% 2.66/0.98  abstr_ref_over_cycles:                  0
% 2.66/0.98  abstr_ref_under_cycles:                 0
% 2.66/0.98  gc_basic_clause_elim:                   0
% 2.66/0.98  forced_gc_time:                         0
% 2.66/0.98  parsing_time:                           0.01
% 2.66/0.98  unif_index_cands_time:                  0.
% 2.66/0.98  unif_index_add_time:                    0.
% 2.66/0.98  orderings_time:                         0.
% 2.66/0.98  out_proof_time:                         0.007
% 2.66/0.98  total_time:                             0.126
% 2.66/0.98  num_of_symbols:                         52
% 2.66/0.98  num_of_terms:                           3232
% 2.66/0.98  
% 2.66/0.98  ------ Preprocessing
% 2.66/0.98  
% 2.66/0.98  num_of_splits:                          0
% 2.66/0.98  num_of_split_atoms:                     0
% 2.66/0.98  num_of_reused_defs:                     0
% 2.66/0.98  num_eq_ax_congr_red:                    34
% 2.66/0.98  num_of_sem_filtered_clauses:            1
% 2.66/0.98  num_of_subtypes:                        0
% 2.66/0.98  monotx_restored_types:                  0
% 2.66/0.98  sat_num_of_epr_types:                   0
% 2.66/0.98  sat_num_of_non_cyclic_types:            0
% 2.66/0.98  sat_guarded_non_collapsed_types:        0
% 2.66/0.98  num_pure_diseq_elim:                    0
% 2.66/0.98  simp_replaced_by:                       0
% 2.66/0.98  res_preprocessed:                       95
% 2.66/0.98  prep_upred:                             0
% 2.66/0.98  prep_unflattend:                        15
% 2.66/0.98  smt_new_axioms:                         0
% 2.66/0.98  pred_elim_cands:                        2
% 2.66/0.98  pred_elim:                              4
% 2.66/0.98  pred_elim_cl:                           4
% 2.66/0.98  pred_elim_cycles:                       6
% 2.66/0.98  merged_defs:                            0
% 2.66/0.98  merged_defs_ncl:                        0
% 2.66/0.98  bin_hyper_res:                          0
% 2.66/0.98  prep_cycles:                            4
% 2.66/0.98  pred_elim_time:                         0.004
% 2.66/0.98  splitting_time:                         0.
% 2.66/0.98  sem_filter_time:                        0.
% 2.66/0.98  monotx_time:                            0.
% 2.66/0.98  subtype_inf_time:                       0.
% 2.66/0.98  
% 2.66/0.98  ------ Problem properties
% 2.66/0.98  
% 2.66/0.98  clauses:                                15
% 2.66/0.98  conjectures:                            2
% 2.66/0.98  epr:                                    0
% 2.66/0.98  horn:                                   15
% 2.66/0.98  ground:                                 2
% 2.66/0.98  unary:                                  12
% 2.66/0.98  binary:                                 2
% 2.66/0.98  lits:                                   19
% 2.66/0.98  lits_eq:                                11
% 2.66/0.98  fd_pure:                                0
% 2.66/0.98  fd_pseudo:                              0
% 2.66/0.98  fd_cond:                                0
% 2.66/0.98  fd_pseudo_cond:                         0
% 2.66/0.98  ac_symbols:                             0
% 2.66/0.98  
% 2.66/0.98  ------ Propositional Solver
% 2.66/0.98  
% 2.66/0.98  prop_solver_calls:                      28
% 2.66/0.98  prop_fast_solver_calls:                 412
% 2.66/0.98  smt_solver_calls:                       0
% 2.66/0.98  smt_fast_solver_calls:                  0
% 2.66/0.98  prop_num_of_clauses:                    1237
% 2.66/0.98  prop_preprocess_simplified:             3486
% 2.66/0.98  prop_fo_subsumed:                       2
% 2.66/0.98  prop_solver_time:                       0.
% 2.66/0.98  smt_solver_time:                        0.
% 2.66/0.98  smt_fast_solver_time:                   0.
% 2.66/0.98  prop_fast_solver_time:                  0.
% 2.66/0.98  prop_unsat_core_time:                   0.
% 2.66/0.98  
% 2.66/0.98  ------ QBF
% 2.66/0.98  
% 2.66/0.98  qbf_q_res:                              0
% 2.66/0.98  qbf_num_tautologies:                    0
% 2.66/0.98  qbf_prep_cycles:                        0
% 2.66/0.98  
% 2.66/0.98  ------ BMC1
% 2.66/0.98  
% 2.66/0.98  bmc1_current_bound:                     -1
% 2.66/0.98  bmc1_last_solved_bound:                 -1
% 2.66/0.98  bmc1_unsat_core_size:                   -1
% 2.66/0.98  bmc1_unsat_core_parents_size:           -1
% 2.66/0.98  bmc1_merge_next_fun:                    0
% 2.66/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.66/0.98  
% 2.66/0.98  ------ Instantiation
% 2.66/0.98  
% 2.66/0.98  inst_num_of_clauses:                    418
% 2.66/0.98  inst_num_in_passive:                    66
% 2.66/0.98  inst_num_in_active:                     195
% 2.66/0.98  inst_num_in_unprocessed:                157
% 2.66/0.98  inst_num_of_loops:                      200
% 2.66/0.98  inst_num_of_learning_restarts:          0
% 2.66/0.98  inst_num_moves_active_passive:          1
% 2.66/0.98  inst_lit_activity:                      0
% 2.66/0.98  inst_lit_activity_moves:                0
% 2.66/0.98  inst_num_tautologies:                   0
% 2.66/0.98  inst_num_prop_implied:                  0
% 2.66/0.98  inst_num_existing_simplified:           0
% 2.66/0.98  inst_num_eq_res_simplified:             0
% 2.66/0.98  inst_num_child_elim:                    0
% 2.66/0.98  inst_num_of_dismatching_blockings:      54
% 2.66/0.98  inst_num_of_non_proper_insts:           326
% 2.66/0.98  inst_num_of_duplicates:                 0
% 2.66/0.98  inst_inst_num_from_inst_to_res:         0
% 2.66/0.98  inst_dismatching_checking_time:         0.
% 2.66/0.98  
% 2.66/0.98  ------ Resolution
% 2.66/0.98  
% 2.66/0.98  res_num_of_clauses:                     0
% 2.66/0.98  res_num_in_passive:                     0
% 2.66/0.98  res_num_in_active:                      0
% 2.66/0.98  res_num_of_loops:                       99
% 2.66/0.98  res_forward_subset_subsumed:            38
% 2.66/0.98  res_backward_subset_subsumed:           0
% 2.66/0.98  res_forward_subsumed:                   0
% 2.66/0.98  res_backward_subsumed:                  0
% 2.66/0.98  res_forward_subsumption_resolution:     0
% 2.66/0.98  res_backward_subsumption_resolution:    0
% 2.66/0.98  res_clause_to_clause_subsumption:       238
% 2.66/0.98  res_orphan_elimination:                 0
% 2.66/0.98  res_tautology_del:                      42
% 2.66/0.98  res_num_eq_res_simplified:              0
% 2.66/0.98  res_num_sel_changes:                    0
% 2.66/0.98  res_moves_from_active_to_pass:          0
% 2.66/0.98  
% 2.66/0.98  ------ Superposition
% 2.66/0.98  
% 2.66/0.98  sup_time_total:                         0.
% 2.66/0.98  sup_time_generating:                    0.
% 2.66/0.98  sup_time_sim_full:                      0.
% 2.66/0.98  sup_time_sim_immed:                     0.
% 2.66/0.98  
% 2.66/0.98  sup_num_of_clauses:                     88
% 2.66/0.98  sup_num_in_active:                      35
% 2.66/0.98  sup_num_in_passive:                     53
% 2.66/0.98  sup_num_of_loops:                       38
% 2.66/0.98  sup_fw_superposition:                   96
% 2.66/0.98  sup_bw_superposition:                   70
% 2.66/0.98  sup_immediate_simplified:               61
% 2.66/0.98  sup_given_eliminated:                   1
% 2.66/0.98  comparisons_done:                       0
% 2.66/0.98  comparisons_avoided:                    0
% 2.66/0.98  
% 2.66/0.98  ------ Simplifications
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  sim_fw_subset_subsumed:                 0
% 2.66/0.98  sim_bw_subset_subsumed:                 0
% 2.66/0.98  sim_fw_subsumed:                        7
% 2.66/0.98  sim_bw_subsumed:                        0
% 2.66/0.98  sim_fw_subsumption_res:                 0
% 2.66/0.98  sim_bw_subsumption_res:                 0
% 2.66/0.98  sim_tautology_del:                      0
% 2.66/0.98  sim_eq_tautology_del:                   2
% 2.66/0.98  sim_eq_res_simp:                        0
% 2.66/0.98  sim_fw_demodulated:                     16
% 2.66/0.98  sim_bw_demodulated:                     6
% 2.66/0.98  sim_light_normalised:                   47
% 2.66/0.98  sim_joinable_taut:                      0
% 2.66/0.98  sim_joinable_simp:                      0
% 2.66/0.98  sim_ac_normalised:                      0
% 2.66/0.98  sim_smt_subsumption:                    0
% 2.66/0.98  
%------------------------------------------------------------------------------
