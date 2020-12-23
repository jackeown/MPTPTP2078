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
% DateTime   : Thu Dec  3 11:55:24 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 214 expanded)
%              Number of clauses        :   71 (  89 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  286 ( 580 expanded)
%              Number of equality atoms :  102 ( 170 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK0,sK1,sK2) != sK1
        | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k2_relset_1(sK0,sK1,sK2) != sK1
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33])).

fof(f55,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1466,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1465,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( r1_tarski(X0,k2_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1469,plain,
    ( r1_tarski(X0,k2_relset_1(X1,X2,X3)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X3) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3589,plain,
    ( r1_tarski(X0,k2_relset_1(sK0,sK1,sK2)) = iProver_top
    | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_1469])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1471,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2787,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1465,c_1471])).

cnf(c_3592,plain,
    ( r1_tarski(X0,k2_relat_1(sK2)) = iProver_top
    | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3589,c_2787])).

cnf(c_3822,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_3592])).

cnf(c_16,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1470,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1472,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2765,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1472])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1473,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3615,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2765,c_1473])).

cnf(c_5,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_58,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5421,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3615,c_58])).

cnf(c_5422,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5421])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1474,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5428,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5422,c_1474])).

cnf(c_5446,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5428,c_58])).

cnf(c_5447,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5446])).

cnf(c_5459,plain,
    ( k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k6_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_3822,c_5447])).

cnf(c_1477,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1475,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2114,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1477,c_1475])).

cnf(c_5604,plain,
    ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_5459,c_2114])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_280,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_4])).

cnf(c_1462,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_1850,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_1462])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1611,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1612,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1611])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_164,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_202,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_164])).

cnf(c_1619,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_1971,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_1972,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2171,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2172,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(c_2203,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1850,c_22,c_1612,c_1972,c_2172])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_164])).

cnf(c_1463,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_2443,plain,
    ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2203,c_1463])).

cnf(c_5605,plain,
    ( k2_relat_1(k6_relat_1(sK1)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5604,c_2443])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5606,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_5605,c_10])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1467,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3141,plain,
    ( k2_relat_1(sK2) != sK1
    | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2787,c_1467])).

cnf(c_18,plain,
    ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1716,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | r1_tarski(sK1,k1_relset_1(X0,X1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1776,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1716])).

cnf(c_1777,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2) != iProver_top
    | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_23,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5606,c_3141,c_1777,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:06:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.69/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/0.98  
% 2.69/0.98  ------  iProver source info
% 2.69/0.98  
% 2.69/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.69/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/0.98  git: non_committed_changes: false
% 2.69/0.98  git: last_make_outside_of_git: false
% 2.69/0.98  
% 2.69/0.98  ------ 
% 2.69/0.98  
% 2.69/0.98  ------ Input Options
% 2.69/0.98  
% 2.69/0.98  --out_options                           all
% 2.69/0.98  --tptp_safe_out                         true
% 2.69/0.98  --problem_path                          ""
% 2.69/0.98  --include_path                          ""
% 2.69/0.98  --clausifier                            res/vclausify_rel
% 2.69/0.98  --clausifier_options                    --mode clausify
% 2.69/0.98  --stdin                                 false
% 2.69/0.98  --stats_out                             all
% 2.69/0.98  
% 2.69/0.98  ------ General Options
% 2.69/0.98  
% 2.69/0.98  --fof                                   false
% 2.69/0.98  --time_out_real                         305.
% 2.69/0.98  --time_out_virtual                      -1.
% 2.69/0.98  --symbol_type_check                     false
% 2.69/0.98  --clausify_out                          false
% 2.69/0.98  --sig_cnt_out                           false
% 2.69/0.98  --trig_cnt_out                          false
% 2.69/0.98  --trig_cnt_out_tolerance                1.
% 2.69/0.98  --trig_cnt_out_sk_spl                   false
% 2.69/0.98  --abstr_cl_out                          false
% 2.69/0.98  
% 2.69/0.98  ------ Global Options
% 2.69/0.98  
% 2.69/0.98  --schedule                              default
% 2.69/0.98  --add_important_lit                     false
% 2.69/0.98  --prop_solver_per_cl                    1000
% 2.69/0.98  --min_unsat_core                        false
% 2.69/0.98  --soft_assumptions                      false
% 2.69/0.98  --soft_lemma_size                       3
% 2.69/0.98  --prop_impl_unit_size                   0
% 2.69/0.98  --prop_impl_unit                        []
% 2.69/0.98  --share_sel_clauses                     true
% 2.69/0.98  --reset_solvers                         false
% 2.69/0.98  --bc_imp_inh                            [conj_cone]
% 2.69/0.98  --conj_cone_tolerance                   3.
% 2.69/0.98  --extra_neg_conj                        none
% 2.69/0.98  --large_theory_mode                     true
% 2.69/0.98  --prolific_symb_bound                   200
% 2.69/0.98  --lt_threshold                          2000
% 2.69/0.98  --clause_weak_htbl                      true
% 2.69/0.98  --gc_record_bc_elim                     false
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing Options
% 2.69/0.98  
% 2.69/0.98  --preprocessing_flag                    true
% 2.69/0.98  --time_out_prep_mult                    0.1
% 2.69/0.98  --splitting_mode                        input
% 2.69/0.98  --splitting_grd                         true
% 2.69/0.98  --splitting_cvd                         false
% 2.69/0.98  --splitting_cvd_svl                     false
% 2.69/0.98  --splitting_nvd                         32
% 2.69/0.98  --sub_typing                            true
% 2.69/0.98  --prep_gs_sim                           true
% 2.69/0.98  --prep_unflatten                        true
% 2.69/0.98  --prep_res_sim                          true
% 2.69/0.98  --prep_upred                            true
% 2.69/0.98  --prep_sem_filter                       exhaustive
% 2.69/0.98  --prep_sem_filter_out                   false
% 2.69/0.98  --pred_elim                             true
% 2.69/0.98  --res_sim_input                         true
% 2.69/0.98  --eq_ax_congr_red                       true
% 2.69/0.98  --pure_diseq_elim                       true
% 2.69/0.98  --brand_transform                       false
% 2.69/0.98  --non_eq_to_eq                          false
% 2.69/0.98  --prep_def_merge                        true
% 2.69/0.98  --prep_def_merge_prop_impl              false
% 2.69/0.98  --prep_def_merge_mbd                    true
% 2.69/0.98  --prep_def_merge_tr_red                 false
% 2.69/0.98  --prep_def_merge_tr_cl                  false
% 2.69/0.98  --smt_preprocessing                     true
% 2.69/0.98  --smt_ac_axioms                         fast
% 2.69/0.98  --preprocessed_out                      false
% 2.69/0.98  --preprocessed_stats                    false
% 2.69/0.98  
% 2.69/0.98  ------ Abstraction refinement Options
% 2.69/0.98  
% 2.69/0.98  --abstr_ref                             []
% 2.69/0.98  --abstr_ref_prep                        false
% 2.69/0.98  --abstr_ref_until_sat                   false
% 2.69/0.98  --abstr_ref_sig_restrict                funpre
% 2.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.98  --abstr_ref_under                       []
% 2.69/0.98  
% 2.69/0.98  ------ SAT Options
% 2.69/0.98  
% 2.69/0.98  --sat_mode                              false
% 2.69/0.98  --sat_fm_restart_options                ""
% 2.69/0.98  --sat_gr_def                            false
% 2.69/0.98  --sat_epr_types                         true
% 2.69/0.98  --sat_non_cyclic_types                  false
% 2.69/0.98  --sat_finite_models                     false
% 2.69/0.98  --sat_fm_lemmas                         false
% 2.69/0.98  --sat_fm_prep                           false
% 2.69/0.98  --sat_fm_uc_incr                        true
% 2.69/0.98  --sat_out_model                         small
% 2.69/0.98  --sat_out_clauses                       false
% 2.69/0.98  
% 2.69/0.98  ------ QBF Options
% 2.69/0.98  
% 2.69/0.98  --qbf_mode                              false
% 2.69/0.98  --qbf_elim_univ                         false
% 2.69/0.98  --qbf_dom_inst                          none
% 2.69/0.98  --qbf_dom_pre_inst                      false
% 2.69/0.98  --qbf_sk_in                             false
% 2.69/0.98  --qbf_pred_elim                         true
% 2.69/0.98  --qbf_split                             512
% 2.69/0.98  
% 2.69/0.98  ------ BMC1 Options
% 2.69/0.98  
% 2.69/0.98  --bmc1_incremental                      false
% 2.69/0.98  --bmc1_axioms                           reachable_all
% 2.69/0.98  --bmc1_min_bound                        0
% 2.69/0.98  --bmc1_max_bound                        -1
% 2.69/0.98  --bmc1_max_bound_default                -1
% 2.69/0.98  --bmc1_symbol_reachability              true
% 2.69/0.98  --bmc1_property_lemmas                  false
% 2.69/0.98  --bmc1_k_induction                      false
% 2.69/0.98  --bmc1_non_equiv_states                 false
% 2.69/0.98  --bmc1_deadlock                         false
% 2.69/0.98  --bmc1_ucm                              false
% 2.69/0.98  --bmc1_add_unsat_core                   none
% 2.69/0.98  --bmc1_unsat_core_children              false
% 2.69/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.98  --bmc1_out_stat                         full
% 2.69/0.98  --bmc1_ground_init                      false
% 2.69/0.98  --bmc1_pre_inst_next_state              false
% 2.69/0.98  --bmc1_pre_inst_state                   false
% 2.69/0.98  --bmc1_pre_inst_reach_state             false
% 2.69/0.98  --bmc1_out_unsat_core                   false
% 2.69/0.98  --bmc1_aig_witness_out                  false
% 2.69/0.98  --bmc1_verbose                          false
% 2.69/0.98  --bmc1_dump_clauses_tptp                false
% 2.69/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.98  --bmc1_dump_file                        -
% 2.69/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.98  --bmc1_ucm_extend_mode                  1
% 2.69/0.98  --bmc1_ucm_init_mode                    2
% 2.69/0.98  --bmc1_ucm_cone_mode                    none
% 2.69/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.98  --bmc1_ucm_relax_model                  4
% 2.69/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.98  --bmc1_ucm_layered_model                none
% 2.69/0.98  --bmc1_ucm_max_lemma_size               10
% 2.69/0.98  
% 2.69/0.98  ------ AIG Options
% 2.69/0.98  
% 2.69/0.98  --aig_mode                              false
% 2.69/0.98  
% 2.69/0.98  ------ Instantiation Options
% 2.69/0.98  
% 2.69/0.98  --instantiation_flag                    true
% 2.69/0.98  --inst_sos_flag                         false
% 2.69/0.98  --inst_sos_phase                        true
% 2.69/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.98  --inst_lit_sel_side                     num_symb
% 2.69/0.98  --inst_solver_per_active                1400
% 2.69/0.98  --inst_solver_calls_frac                1.
% 2.69/0.98  --inst_passive_queue_type               priority_queues
% 2.69/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.98  --inst_passive_queues_freq              [25;2]
% 2.69/0.98  --inst_dismatching                      true
% 2.69/0.98  --inst_eager_unprocessed_to_passive     true
% 2.69/0.98  --inst_prop_sim_given                   true
% 2.69/0.98  --inst_prop_sim_new                     false
% 2.69/0.98  --inst_subs_new                         false
% 2.69/0.98  --inst_eq_res_simp                      false
% 2.69/0.98  --inst_subs_given                       false
% 2.69/0.98  --inst_orphan_elimination               true
% 2.69/0.98  --inst_learning_loop_flag               true
% 2.69/0.98  --inst_learning_start                   3000
% 2.69/0.98  --inst_learning_factor                  2
% 2.69/0.98  --inst_start_prop_sim_after_learn       3
% 2.69/0.98  --inst_sel_renew                        solver
% 2.69/0.98  --inst_lit_activity_flag                true
% 2.69/0.98  --inst_restr_to_given                   false
% 2.69/0.98  --inst_activity_threshold               500
% 2.69/0.98  --inst_out_proof                        true
% 2.69/0.98  
% 2.69/0.98  ------ Resolution Options
% 2.69/0.98  
% 2.69/0.98  --resolution_flag                       true
% 2.69/0.98  --res_lit_sel                           adaptive
% 2.69/0.98  --res_lit_sel_side                      none
% 2.69/0.98  --res_ordering                          kbo
% 2.69/0.98  --res_to_prop_solver                    active
% 2.69/0.98  --res_prop_simpl_new                    false
% 2.69/0.98  --res_prop_simpl_given                  true
% 2.69/0.98  --res_passive_queue_type                priority_queues
% 2.69/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.98  --res_passive_queues_freq               [15;5]
% 2.69/0.98  --res_forward_subs                      full
% 2.69/0.98  --res_backward_subs                     full
% 2.69/0.98  --res_forward_subs_resolution           true
% 2.69/0.98  --res_backward_subs_resolution          true
% 2.69/0.98  --res_orphan_elimination                true
% 2.69/0.98  --res_time_limit                        2.
% 2.69/0.98  --res_out_proof                         true
% 2.69/0.98  
% 2.69/0.98  ------ Superposition Options
% 2.69/0.98  
% 2.69/0.98  --superposition_flag                    true
% 2.69/0.98  --sup_passive_queue_type                priority_queues
% 2.69/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.98  --demod_completeness_check              fast
% 2.69/0.98  --demod_use_ground                      true
% 2.69/0.98  --sup_to_prop_solver                    passive
% 2.69/0.98  --sup_prop_simpl_new                    true
% 2.69/0.98  --sup_prop_simpl_given                  true
% 2.69/0.98  --sup_fun_splitting                     false
% 2.69/0.98  --sup_smt_interval                      50000
% 2.69/0.98  
% 2.69/0.98  ------ Superposition Simplification Setup
% 2.69/0.98  
% 2.69/0.98  --sup_indices_passive                   []
% 2.69/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_full_bw                           [BwDemod]
% 2.69/0.98  --sup_immed_triv                        [TrivRules]
% 2.69/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_immed_bw_main                     []
% 2.69/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.98  
% 2.69/0.98  ------ Combination Options
% 2.69/0.98  
% 2.69/0.98  --comb_res_mult                         3
% 2.69/0.98  --comb_sup_mult                         2
% 2.69/0.98  --comb_inst_mult                        10
% 2.69/0.98  
% 2.69/0.98  ------ Debug Options
% 2.69/0.98  
% 2.69/0.98  --dbg_backtrace                         false
% 2.69/0.98  --dbg_dump_prop_clauses                 false
% 2.69/0.98  --dbg_dump_prop_clauses_file            -
% 2.69/0.98  --dbg_out_stat                          false
% 2.69/0.98  ------ Parsing...
% 2.69/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/0.98  ------ Proving...
% 2.69/0.98  ------ Problem Properties 
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  clauses                                 20
% 2.69/0.98  conjectures                             3
% 2.69/0.98  EPR                                     2
% 2.69/0.98  Horn                                    20
% 2.69/0.98  unary                                   7
% 2.69/0.98  binary                                  7
% 2.69/0.98  lits                                    40
% 2.69/0.98  lits eq                                 7
% 2.69/0.98  fd_pure                                 0
% 2.69/0.98  fd_pseudo                               0
% 2.69/0.98  fd_cond                                 0
% 2.69/0.98  fd_pseudo_cond                          0
% 2.69/0.98  AC symbols                              0
% 2.69/0.98  
% 2.69/0.98  ------ Schedule dynamic 5 is on 
% 2.69/0.98  
% 2.69/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  ------ 
% 2.69/0.98  Current options:
% 2.69/0.98  ------ 
% 2.69/0.98  
% 2.69/0.98  ------ Input Options
% 2.69/0.98  
% 2.69/0.98  --out_options                           all
% 2.69/0.98  --tptp_safe_out                         true
% 2.69/0.98  --problem_path                          ""
% 2.69/0.98  --include_path                          ""
% 2.69/0.98  --clausifier                            res/vclausify_rel
% 2.69/0.98  --clausifier_options                    --mode clausify
% 2.69/0.98  --stdin                                 false
% 2.69/0.98  --stats_out                             all
% 2.69/0.98  
% 2.69/0.98  ------ General Options
% 2.69/0.98  
% 2.69/0.98  --fof                                   false
% 2.69/0.98  --time_out_real                         305.
% 2.69/0.98  --time_out_virtual                      -1.
% 2.69/0.98  --symbol_type_check                     false
% 2.69/0.98  --clausify_out                          false
% 2.69/0.98  --sig_cnt_out                           false
% 2.69/0.98  --trig_cnt_out                          false
% 2.69/0.98  --trig_cnt_out_tolerance                1.
% 2.69/0.98  --trig_cnt_out_sk_spl                   false
% 2.69/0.98  --abstr_cl_out                          false
% 2.69/0.98  
% 2.69/0.98  ------ Global Options
% 2.69/0.98  
% 2.69/0.98  --schedule                              default
% 2.69/0.98  --add_important_lit                     false
% 2.69/0.98  --prop_solver_per_cl                    1000
% 2.69/0.98  --min_unsat_core                        false
% 2.69/0.98  --soft_assumptions                      false
% 2.69/0.98  --soft_lemma_size                       3
% 2.69/0.98  --prop_impl_unit_size                   0
% 2.69/0.98  --prop_impl_unit                        []
% 2.69/0.98  --share_sel_clauses                     true
% 2.69/0.98  --reset_solvers                         false
% 2.69/0.98  --bc_imp_inh                            [conj_cone]
% 2.69/0.98  --conj_cone_tolerance                   3.
% 2.69/0.98  --extra_neg_conj                        none
% 2.69/0.98  --large_theory_mode                     true
% 2.69/0.98  --prolific_symb_bound                   200
% 2.69/0.98  --lt_threshold                          2000
% 2.69/0.98  --clause_weak_htbl                      true
% 2.69/0.98  --gc_record_bc_elim                     false
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing Options
% 2.69/0.98  
% 2.69/0.98  --preprocessing_flag                    true
% 2.69/0.98  --time_out_prep_mult                    0.1
% 2.69/0.98  --splitting_mode                        input
% 2.69/0.98  --splitting_grd                         true
% 2.69/0.98  --splitting_cvd                         false
% 2.69/0.98  --splitting_cvd_svl                     false
% 2.69/0.98  --splitting_nvd                         32
% 2.69/0.98  --sub_typing                            true
% 2.69/0.98  --prep_gs_sim                           true
% 2.69/0.98  --prep_unflatten                        true
% 2.69/0.98  --prep_res_sim                          true
% 2.69/0.98  --prep_upred                            true
% 2.69/0.98  --prep_sem_filter                       exhaustive
% 2.69/0.98  --prep_sem_filter_out                   false
% 2.69/0.98  --pred_elim                             true
% 2.69/0.98  --res_sim_input                         true
% 2.69/0.98  --eq_ax_congr_red                       true
% 2.69/0.98  --pure_diseq_elim                       true
% 2.69/0.98  --brand_transform                       false
% 2.69/0.98  --non_eq_to_eq                          false
% 2.69/0.98  --prep_def_merge                        true
% 2.69/0.98  --prep_def_merge_prop_impl              false
% 2.69/0.98  --prep_def_merge_mbd                    true
% 2.69/0.98  --prep_def_merge_tr_red                 false
% 2.69/0.98  --prep_def_merge_tr_cl                  false
% 2.69/0.98  --smt_preprocessing                     true
% 2.69/0.98  --smt_ac_axioms                         fast
% 2.69/0.98  --preprocessed_out                      false
% 2.69/0.98  --preprocessed_stats                    false
% 2.69/0.98  
% 2.69/0.98  ------ Abstraction refinement Options
% 2.69/0.98  
% 2.69/0.98  --abstr_ref                             []
% 2.69/0.98  --abstr_ref_prep                        false
% 2.69/0.98  --abstr_ref_until_sat                   false
% 2.69/0.98  --abstr_ref_sig_restrict                funpre
% 2.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.98  --abstr_ref_under                       []
% 2.69/0.98  
% 2.69/0.98  ------ SAT Options
% 2.69/0.98  
% 2.69/0.98  --sat_mode                              false
% 2.69/0.98  --sat_fm_restart_options                ""
% 2.69/0.98  --sat_gr_def                            false
% 2.69/0.98  --sat_epr_types                         true
% 2.69/0.98  --sat_non_cyclic_types                  false
% 2.69/0.98  --sat_finite_models                     false
% 2.69/0.98  --sat_fm_lemmas                         false
% 2.69/0.98  --sat_fm_prep                           false
% 2.69/0.98  --sat_fm_uc_incr                        true
% 2.69/0.98  --sat_out_model                         small
% 2.69/0.98  --sat_out_clauses                       false
% 2.69/0.98  
% 2.69/0.98  ------ QBF Options
% 2.69/0.98  
% 2.69/0.98  --qbf_mode                              false
% 2.69/0.98  --qbf_elim_univ                         false
% 2.69/0.98  --qbf_dom_inst                          none
% 2.69/0.98  --qbf_dom_pre_inst                      false
% 2.69/0.98  --qbf_sk_in                             false
% 2.69/0.98  --qbf_pred_elim                         true
% 2.69/0.98  --qbf_split                             512
% 2.69/0.98  
% 2.69/0.98  ------ BMC1 Options
% 2.69/0.98  
% 2.69/0.98  --bmc1_incremental                      false
% 2.69/0.98  --bmc1_axioms                           reachable_all
% 2.69/0.98  --bmc1_min_bound                        0
% 2.69/0.98  --bmc1_max_bound                        -1
% 2.69/0.98  --bmc1_max_bound_default                -1
% 2.69/0.98  --bmc1_symbol_reachability              true
% 2.69/0.98  --bmc1_property_lemmas                  false
% 2.69/0.98  --bmc1_k_induction                      false
% 2.69/0.98  --bmc1_non_equiv_states                 false
% 2.69/0.98  --bmc1_deadlock                         false
% 2.69/0.98  --bmc1_ucm                              false
% 2.69/0.98  --bmc1_add_unsat_core                   none
% 2.69/0.98  --bmc1_unsat_core_children              false
% 2.69/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.98  --bmc1_out_stat                         full
% 2.69/0.98  --bmc1_ground_init                      false
% 2.69/0.98  --bmc1_pre_inst_next_state              false
% 2.69/0.98  --bmc1_pre_inst_state                   false
% 2.69/0.98  --bmc1_pre_inst_reach_state             false
% 2.69/0.98  --bmc1_out_unsat_core                   false
% 2.69/0.98  --bmc1_aig_witness_out                  false
% 2.69/0.98  --bmc1_verbose                          false
% 2.69/0.98  --bmc1_dump_clauses_tptp                false
% 2.69/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.98  --bmc1_dump_file                        -
% 2.69/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.98  --bmc1_ucm_extend_mode                  1
% 2.69/0.98  --bmc1_ucm_init_mode                    2
% 2.69/0.98  --bmc1_ucm_cone_mode                    none
% 2.69/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.98  --bmc1_ucm_relax_model                  4
% 2.69/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.98  --bmc1_ucm_layered_model                none
% 2.69/0.98  --bmc1_ucm_max_lemma_size               10
% 2.69/0.98  
% 2.69/0.98  ------ AIG Options
% 2.69/0.98  
% 2.69/0.98  --aig_mode                              false
% 2.69/0.98  
% 2.69/0.98  ------ Instantiation Options
% 2.69/0.98  
% 2.69/0.98  --instantiation_flag                    true
% 2.69/0.98  --inst_sos_flag                         false
% 2.69/0.98  --inst_sos_phase                        true
% 2.69/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.98  --inst_lit_sel_side                     none
% 2.69/0.98  --inst_solver_per_active                1400
% 2.69/0.98  --inst_solver_calls_frac                1.
% 2.69/0.98  --inst_passive_queue_type               priority_queues
% 2.69/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.98  --inst_passive_queues_freq              [25;2]
% 2.69/0.98  --inst_dismatching                      true
% 2.69/0.98  --inst_eager_unprocessed_to_passive     true
% 2.69/0.98  --inst_prop_sim_given                   true
% 2.69/0.98  --inst_prop_sim_new                     false
% 2.69/0.98  --inst_subs_new                         false
% 2.69/0.98  --inst_eq_res_simp                      false
% 2.69/0.98  --inst_subs_given                       false
% 2.69/0.98  --inst_orphan_elimination               true
% 2.69/0.98  --inst_learning_loop_flag               true
% 2.69/0.98  --inst_learning_start                   3000
% 2.69/0.98  --inst_learning_factor                  2
% 2.69/0.98  --inst_start_prop_sim_after_learn       3
% 2.69/0.98  --inst_sel_renew                        solver
% 2.69/0.98  --inst_lit_activity_flag                true
% 2.69/0.98  --inst_restr_to_given                   false
% 2.69/0.98  --inst_activity_threshold               500
% 2.69/0.98  --inst_out_proof                        true
% 2.69/0.98  
% 2.69/0.98  ------ Resolution Options
% 2.69/0.98  
% 2.69/0.98  --resolution_flag                       false
% 2.69/0.98  --res_lit_sel                           adaptive
% 2.69/0.98  --res_lit_sel_side                      none
% 2.69/0.98  --res_ordering                          kbo
% 2.69/0.98  --res_to_prop_solver                    active
% 2.69/0.98  --res_prop_simpl_new                    false
% 2.69/0.98  --res_prop_simpl_given                  true
% 2.69/0.98  --res_passive_queue_type                priority_queues
% 2.69/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.98  --res_passive_queues_freq               [15;5]
% 2.69/0.98  --res_forward_subs                      full
% 2.69/0.98  --res_backward_subs                     full
% 2.69/0.98  --res_forward_subs_resolution           true
% 2.69/0.98  --res_backward_subs_resolution          true
% 2.69/0.98  --res_orphan_elimination                true
% 2.69/0.98  --res_time_limit                        2.
% 2.69/0.98  --res_out_proof                         true
% 2.69/0.98  
% 2.69/0.98  ------ Superposition Options
% 2.69/0.98  
% 2.69/0.98  --superposition_flag                    true
% 2.69/0.98  --sup_passive_queue_type                priority_queues
% 2.69/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.98  --demod_completeness_check              fast
% 2.69/0.98  --demod_use_ground                      true
% 2.69/0.98  --sup_to_prop_solver                    passive
% 2.69/0.98  --sup_prop_simpl_new                    true
% 2.69/0.98  --sup_prop_simpl_given                  true
% 2.69/0.98  --sup_fun_splitting                     false
% 2.69/0.98  --sup_smt_interval                      50000
% 2.69/0.98  
% 2.69/0.98  ------ Superposition Simplification Setup
% 2.69/0.98  
% 2.69/0.98  --sup_indices_passive                   []
% 2.69/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_full_bw                           [BwDemod]
% 2.69/0.98  --sup_immed_triv                        [TrivRules]
% 2.69/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_immed_bw_main                     []
% 2.69/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.98  
% 2.69/0.98  ------ Combination Options
% 2.69/0.98  
% 2.69/0.98  --comb_res_mult                         3
% 2.69/0.98  --comb_sup_mult                         2
% 2.69/0.98  --comb_inst_mult                        10
% 2.69/0.98  
% 2.69/0.98  ------ Debug Options
% 2.69/0.98  
% 2.69/0.98  --dbg_backtrace                         false
% 2.69/0.98  --dbg_dump_prop_clauses                 false
% 2.69/0.98  --dbg_dump_prop_clauses_file            -
% 2.69/0.98  --dbg_out_stat                          false
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  ------ Proving...
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  % SZS status Theorem for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  fof(f15,conjecture,(
% 2.69/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f16,negated_conjecture,(
% 2.69/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 2.69/0.98    inference(negated_conjecture,[],[f15])).
% 2.69/0.98  
% 2.69/0.98  fof(f29,plain,(
% 2.69/0.98    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.98    inference(ennf_transformation,[],[f16])).
% 2.69/0.98  
% 2.69/0.98  fof(f30,plain,(
% 2.69/0.98    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.98    inference(flattening,[],[f29])).
% 2.69/0.98  
% 2.69/0.98  fof(f33,plain,(
% 2.69/0.98    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f34,plain,(
% 2.69/0.98    (k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33])).
% 2.69/0.98  
% 2.69/0.98  fof(f55,plain,(
% 2.69/0.98    r1_tarski(k6_relat_1(sK1),sK2)),
% 2.69/0.98    inference(cnf_transformation,[],[f34])).
% 2.69/0.98  
% 2.69/0.98  fof(f54,plain,(
% 2.69/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.69/0.98    inference(cnf_transformation,[],[f34])).
% 2.69/0.98  
% 2.69/0.98  fof(f14,axiom,(
% 2.69/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f27,plain,(
% 2.69/0.98    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.98    inference(ennf_transformation,[],[f14])).
% 2.69/0.98  
% 2.69/0.98  fof(f28,plain,(
% 2.69/0.98    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.98    inference(flattening,[],[f27])).
% 2.69/0.98  
% 2.69/0.98  fof(f53,plain,(
% 2.69/0.98    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f28])).
% 2.69/0.98  
% 2.69/0.98  fof(f12,axiom,(
% 2.69/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f26,plain,(
% 2.69/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.98    inference(ennf_transformation,[],[f12])).
% 2.69/0.98  
% 2.69/0.98  fof(f50,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f26])).
% 2.69/0.98  
% 2.69/0.98  fof(f13,axiom,(
% 2.69/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f51,plain,(
% 2.69/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f13])).
% 2.69/0.98  
% 2.69/0.98  fof(f11,axiom,(
% 2.69/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f25,plain,(
% 2.69/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.98    inference(ennf_transformation,[],[f11])).
% 2.69/0.98  
% 2.69/0.98  fof(f48,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f25])).
% 2.69/0.98  
% 2.69/0.98  fof(f8,axiom,(
% 2.69/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f22,plain,(
% 2.69/0.98    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 2.69/0.98    inference(ennf_transformation,[],[f8])).
% 2.69/0.98  
% 2.69/0.98  fof(f23,plain,(
% 2.69/0.98    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 2.69/0.98    inference(flattening,[],[f22])).
% 2.69/0.98  
% 2.69/0.98  fof(f44,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f23])).
% 2.69/0.98  
% 2.69/0.98  fof(f4,axiom,(
% 2.69/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f40,plain,(
% 2.69/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f4])).
% 2.69/0.98  
% 2.69/0.98  fof(f7,axiom,(
% 2.69/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f20,plain,(
% 2.69/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.69/0.98    inference(ennf_transformation,[],[f7])).
% 2.69/0.98  
% 2.69/0.98  fof(f21,plain,(
% 2.69/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/0.98    inference(flattening,[],[f20])).
% 2.69/0.98  
% 2.69/0.98  fof(f43,plain,(
% 2.69/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f21])).
% 2.69/0.98  
% 2.69/0.98  fof(f6,axiom,(
% 2.69/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f19,plain,(
% 2.69/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/0.98    inference(ennf_transformation,[],[f6])).
% 2.69/0.98  
% 2.69/0.98  fof(f42,plain,(
% 2.69/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f19])).
% 2.69/0.98  
% 2.69/0.98  fof(f49,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f25])).
% 2.69/0.98  
% 2.69/0.98  fof(f3,axiom,(
% 2.69/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f18,plain,(
% 2.69/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.69/0.98    inference(ennf_transformation,[],[f3])).
% 2.69/0.98  
% 2.69/0.98  fof(f32,plain,(
% 2.69/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.69/0.98    inference(nnf_transformation,[],[f18])).
% 2.69/0.98  
% 2.69/0.98  fof(f38,plain,(
% 2.69/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f32])).
% 2.69/0.98  
% 2.69/0.98  fof(f1,axiom,(
% 2.69/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f31,plain,(
% 2.69/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.69/0.98    inference(nnf_transformation,[],[f1])).
% 2.69/0.98  
% 2.69/0.98  fof(f35,plain,(
% 2.69/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f31])).
% 2.69/0.98  
% 2.69/0.98  fof(f2,axiom,(
% 2.69/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f17,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.69/0.98    inference(ennf_transformation,[],[f2])).
% 2.69/0.98  
% 2.69/0.98  fof(f37,plain,(
% 2.69/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f17])).
% 2.69/0.98  
% 2.69/0.98  fof(f36,plain,(
% 2.69/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f31])).
% 2.69/0.98  
% 2.69/0.98  fof(f5,axiom,(
% 2.69/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f41,plain,(
% 2.69/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f5])).
% 2.69/0.98  
% 2.69/0.98  fof(f10,axiom,(
% 2.69/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f24,plain,(
% 2.69/0.98    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f10])).
% 2.69/0.98  
% 2.69/0.98  fof(f47,plain,(
% 2.69/0.98    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f24])).
% 2.69/0.98  
% 2.69/0.98  fof(f9,axiom,(
% 2.69/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f46,plain,(
% 2.69/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.69/0.98    inference(cnf_transformation,[],[f9])).
% 2.69/0.98  
% 2.69/0.98  fof(f56,plain,(
% 2.69/0.98    k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 2.69/0.98    inference(cnf_transformation,[],[f34])).
% 2.69/0.98  
% 2.69/0.98  fof(f52,plain,(
% 2.69/0.98    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.98    inference(cnf_transformation,[],[f28])).
% 2.69/0.98  
% 2.69/0.98  cnf(c_20,negated_conjecture,
% 2.69/0.98      ( r1_tarski(k6_relat_1(sK1),sK2) ),
% 2.69/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1466,plain,
% 2.69/0.98      ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_21,negated_conjecture,
% 2.69/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.69/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1465,plain,
% 2.69/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_17,plain,
% 2.69/0.98      ( r1_tarski(X0,k2_relset_1(X1,X2,X3))
% 2.69/0.98      | ~ r1_tarski(k6_relat_1(X0),X3)
% 2.69/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.69/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1469,plain,
% 2.69/0.98      ( r1_tarski(X0,k2_relset_1(X1,X2,X3)) = iProver_top
% 2.69/0.98      | r1_tarski(k6_relat_1(X0),X3) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3589,plain,
% 2.69/0.98      ( r1_tarski(X0,k2_relset_1(sK0,sK1,sK2)) = iProver_top
% 2.69/0.98      | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_1465,c_1469]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_15,plain,
% 2.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1471,plain,
% 2.69/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.69/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2787,plain,
% 2.69/0.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_1465,c_1471]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3592,plain,
% 2.69/0.98      ( r1_tarski(X0,k2_relat_1(sK2)) = iProver_top
% 2.69/0.98      | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
% 2.69/0.98      inference(light_normalisation,[status(thm)],[c_3589,c_2787]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3822,plain,
% 2.69/0.98      ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_1466,c_3592]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_16,plain,
% 2.69/0.98      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.69/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1470,plain,
% 2.69/0.98      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_14,plain,
% 2.69/0.98      ( v4_relat_1(X0,X1)
% 2.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.69/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1472,plain,
% 2.69/0.98      ( v4_relat_1(X0,X1) = iProver_top
% 2.69/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2765,plain,
% 2.69/0.98      ( v4_relat_1(k6_relat_1(X0),X0) = iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_1470,c_1472]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_9,plain,
% 2.69/0.98      ( ~ v4_relat_1(X0,X1)
% 2.69/0.98      | v4_relat_1(X0,X2)
% 2.69/0.98      | ~ r1_tarski(X1,X2)
% 2.69/0.98      | ~ v1_relat_1(X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1473,plain,
% 2.69/0.98      ( v4_relat_1(X0,X1) != iProver_top
% 2.69/0.98      | v4_relat_1(X0,X2) = iProver_top
% 2.69/0.98      | r1_tarski(X1,X2) != iProver_top
% 2.69/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3615,plain,
% 2.69/0.98      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 2.69/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.69/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_2765,c_1473]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5,plain,
% 2.69/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.69/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_58,plain,
% 2.69/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5421,plain,
% 2.69/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.69/0.98      | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_3615,c_58]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5422,plain,
% 2.69/0.98      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 2.69/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_5421]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_8,plain,
% 2.69/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.69/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1474,plain,
% 2.69/0.98      ( k7_relat_1(X0,X1) = X0
% 2.69/0.98      | v4_relat_1(X0,X1) != iProver_top
% 2.69/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5428,plain,
% 2.69/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 2.69/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.69/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_5422,c_1474]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5446,plain,
% 2.69/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.69/0.98      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_5428,c_58]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5447,plain,
% 2.69/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 2.69/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_5446]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5459,plain,
% 2.69/0.98      ( k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k6_relat_1(sK1) ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_3822,c_5447]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1477,plain,
% 2.69/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_7,plain,
% 2.69/0.98      ( ~ v1_relat_1(X0)
% 2.69/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1475,plain,
% 2.69/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.69/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2114,plain,
% 2.69/0.98      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_1477,c_1475]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5604,plain,
% 2.69/0.98      ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k2_relat_1(k6_relat_1(sK1)) ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_5459,c_2114]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_13,plain,
% 2.69/0.98      ( v5_relat_1(X0,X1)
% 2.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.69/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_4,plain,
% 2.69/0.98      ( ~ v5_relat_1(X0,X1)
% 2.69/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 2.69/0.98      | ~ v1_relat_1(X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_280,plain,
% 2.69/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.69/0.98      | ~ v1_relat_1(X0) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_13,c_4]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1462,plain,
% 2.69/0.98      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 2.69/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.69/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1850,plain,
% 2.69/0.98      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 2.69/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_1465,c_1462]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_22,plain,
% 2.69/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1,plain,
% 2.69/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.69/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1611,plain,
% 2.69/0.98      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 2.69/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1612,plain,
% 2.69/0.98      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 2.69/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_1611]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2,plain,
% 2.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/0.98      | ~ v1_relat_1(X1)
% 2.69/0.98      | v1_relat_1(X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_0,plain,
% 2.69/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.69/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_164,plain,
% 2.69/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.69/0.98      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_202,plain,
% 2.69/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.69/0.98      inference(bin_hyper_res,[status(thm)],[c_2,c_164]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1619,plain,
% 2.69/0.98      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.69/0.98      | v1_relat_1(X0)
% 2.69/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_202]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1971,plain,
% 2.69/0.98      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 2.69/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.69/0.98      | v1_relat_1(sK2) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_1619]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1972,plain,
% 2.69/0.98      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.69/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.69/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_1971]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_6,plain,
% 2.69/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.69/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2171,plain,
% 2.69/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2172,plain,
% 2.69/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2203,plain,
% 2.69/0.98      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_1850,c_22,c_1612,c_1972,c_2172]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_12,plain,
% 2.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/0.98      | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 2.69/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_203,plain,
% 2.69/0.98      ( ~ r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 2.69/0.98      inference(bin_hyper_res,[status(thm)],[c_12,c_164]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1463,plain,
% 2.69/0.98      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 2.69/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2443,plain,
% 2.69/0.98      ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_2203,c_1463]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5605,plain,
% 2.69/0.98      ( k2_relat_1(k6_relat_1(sK1)) = k2_relat_1(sK2) ),
% 2.69/0.98      inference(light_normalisation,[status(thm)],[c_5604,c_2443]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_10,plain,
% 2.69/0.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 2.69/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5606,plain,
% 2.69/0.98      ( k2_relat_1(sK2) = sK1 ),
% 2.69/0.98      inference(demodulation,[status(thm)],[c_5605,c_10]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_19,negated_conjecture,
% 2.69/0.98      ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
% 2.69/0.98      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 2.69/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1467,plain,
% 2.69/0.98      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 2.69/0.98      | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3141,plain,
% 2.69/0.98      ( k2_relat_1(sK2) != sK1
% 2.69/0.98      | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) != iProver_top ),
% 2.69/0.98      inference(demodulation,[status(thm)],[c_2787,c_1467]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_18,plain,
% 2.69/0.98      ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
% 2.69/0.98      | ~ r1_tarski(k6_relat_1(X0),X3)
% 2.69/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.69/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1716,plain,
% 2.69/0.98      ( ~ r1_tarski(k6_relat_1(sK1),sK2)
% 2.69/0.98      | r1_tarski(sK1,k1_relset_1(X0,X1,sK2))
% 2.69/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1776,plain,
% 2.69/0.98      ( ~ r1_tarski(k6_relat_1(sK1),sK2)
% 2.69/0.98      | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
% 2.69/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_1716]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1777,plain,
% 2.69/0.98      ( r1_tarski(k6_relat_1(sK1),sK2) != iProver_top
% 2.69/0.98      | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) = iProver_top
% 2.69/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_23,plain,
% 2.69/0.98      ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(contradiction,plain,
% 2.69/0.98      ( $false ),
% 2.69/0.98      inference(minisat,[status(thm)],[c_5606,c_3141,c_1777,c_23,c_22]) ).
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  ------                               Statistics
% 2.69/0.98  
% 2.69/0.98  ------ General
% 2.69/0.98  
% 2.69/0.98  abstr_ref_over_cycles:                  0
% 2.69/0.98  abstr_ref_under_cycles:                 0
% 2.69/0.98  gc_basic_clause_elim:                   0
% 2.69/0.98  forced_gc_time:                         0
% 2.69/0.98  parsing_time:                           0.008
% 2.69/0.98  unif_index_cands_time:                  0.
% 2.69/0.98  unif_index_add_time:                    0.
% 2.69/0.98  orderings_time:                         0.
% 2.69/0.99  out_proof_time:                         0.007
% 2.69/0.99  total_time:                             0.169
% 2.69/0.99  num_of_symbols:                         48
% 2.69/0.99  num_of_terms:                           5079
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing
% 2.69/0.99  
% 2.69/0.99  num_of_splits:                          0
% 2.69/0.99  num_of_split_atoms:                     0
% 2.69/0.99  num_of_reused_defs:                     0
% 2.69/0.99  num_eq_ax_congr_red:                    17
% 2.69/0.99  num_of_sem_filtered_clauses:            1
% 2.69/0.99  num_of_subtypes:                        0
% 2.69/0.99  monotx_restored_types:                  0
% 2.69/0.99  sat_num_of_epr_types:                   0
% 2.69/0.99  sat_num_of_non_cyclic_types:            0
% 2.69/0.99  sat_guarded_non_collapsed_types:        0
% 2.69/0.99  num_pure_diseq_elim:                    0
% 2.69/0.99  simp_replaced_by:                       0
% 2.69/0.99  res_preprocessed:                       109
% 2.69/0.99  prep_upred:                             0
% 2.69/0.99  prep_unflattend:                        34
% 2.69/0.99  smt_new_axioms:                         0
% 2.69/0.99  pred_elim_cands:                        4
% 2.69/0.99  pred_elim:                              1
% 2.69/0.99  pred_elim_cl:                           2
% 2.69/0.99  pred_elim_cycles:                       3
% 2.69/0.99  merged_defs:                            8
% 2.69/0.99  merged_defs_ncl:                        0
% 2.69/0.99  bin_hyper_res:                          10
% 2.69/0.99  prep_cycles:                            4
% 2.69/0.99  pred_elim_time:                         0.009
% 2.69/0.99  splitting_time:                         0.
% 2.69/0.99  sem_filter_time:                        0.
% 2.69/0.99  monotx_time:                            0.001
% 2.69/0.99  subtype_inf_time:                       0.
% 2.69/0.99  
% 2.69/0.99  ------ Problem properties
% 2.69/0.99  
% 2.69/0.99  clauses:                                20
% 2.69/0.99  conjectures:                            3
% 2.69/0.99  epr:                                    2
% 2.69/0.99  horn:                                   20
% 2.69/0.99  ground:                                 3
% 2.69/0.99  unary:                                  7
% 2.69/0.99  binary:                                 7
% 2.69/0.99  lits:                                   40
% 2.69/0.99  lits_eq:                                7
% 2.69/0.99  fd_pure:                                0
% 2.69/0.99  fd_pseudo:                              0
% 2.69/0.99  fd_cond:                                0
% 2.69/0.99  fd_pseudo_cond:                         0
% 2.69/0.99  ac_symbols:                             0
% 2.69/0.99  
% 2.69/0.99  ------ Propositional Solver
% 2.69/0.99  
% 2.69/0.99  prop_solver_calls:                      27
% 2.69/0.99  prop_fast_solver_calls:                 716
% 2.69/0.99  smt_solver_calls:                       0
% 2.69/0.99  smt_fast_solver_calls:                  0
% 2.69/0.99  prop_num_of_clauses:                    2232
% 2.69/0.99  prop_preprocess_simplified:             6656
% 2.69/0.99  prop_fo_subsumed:                       14
% 2.69/0.99  prop_solver_time:                       0.
% 2.69/0.99  smt_solver_time:                        0.
% 2.69/0.99  smt_fast_solver_time:                   0.
% 2.69/0.99  prop_fast_solver_time:                  0.
% 2.69/0.99  prop_unsat_core_time:                   0.
% 2.69/0.99  
% 2.69/0.99  ------ QBF
% 2.69/0.99  
% 2.69/0.99  qbf_q_res:                              0
% 2.69/0.99  qbf_num_tautologies:                    0
% 2.69/0.99  qbf_prep_cycles:                        0
% 2.69/0.99  
% 2.69/0.99  ------ BMC1
% 2.69/0.99  
% 2.69/0.99  bmc1_current_bound:                     -1
% 2.69/0.99  bmc1_last_solved_bound:                 -1
% 2.69/0.99  bmc1_unsat_core_size:                   -1
% 2.69/0.99  bmc1_unsat_core_parents_size:           -1
% 2.69/0.99  bmc1_merge_next_fun:                    0
% 2.69/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation
% 2.69/0.99  
% 2.69/0.99  inst_num_of_clauses:                    706
% 2.69/0.99  inst_num_in_passive:                    255
% 2.69/0.99  inst_num_in_active:                     321
% 2.69/0.99  inst_num_in_unprocessed:                130
% 2.69/0.99  inst_num_of_loops:                      330
% 2.69/0.99  inst_num_of_learning_restarts:          0
% 2.69/0.99  inst_num_moves_active_passive:          7
% 2.69/0.99  inst_lit_activity:                      0
% 2.69/0.99  inst_lit_activity_moves:                0
% 2.69/0.99  inst_num_tautologies:                   0
% 2.69/0.99  inst_num_prop_implied:                  0
% 2.69/0.99  inst_num_existing_simplified:           0
% 2.69/0.99  inst_num_eq_res_simplified:             0
% 2.69/0.99  inst_num_child_elim:                    0
% 2.69/0.99  inst_num_of_dismatching_blockings:      146
% 2.69/0.99  inst_num_of_non_proper_insts:           501
% 2.69/0.99  inst_num_of_duplicates:                 0
% 2.69/0.99  inst_inst_num_from_inst_to_res:         0
% 2.69/0.99  inst_dismatching_checking_time:         0.
% 2.69/0.99  
% 2.69/0.99  ------ Resolution
% 2.69/0.99  
% 2.69/0.99  res_num_of_clauses:                     0
% 2.69/0.99  res_num_in_passive:                     0
% 2.69/0.99  res_num_in_active:                      0
% 2.69/0.99  res_num_of_loops:                       113
% 2.69/0.99  res_forward_subset_subsumed:            34
% 2.69/0.99  res_backward_subset_subsumed:           0
% 2.69/0.99  res_forward_subsumed:                   0
% 2.69/0.99  res_backward_subsumed:                  0
% 2.69/0.99  res_forward_subsumption_resolution:     0
% 2.69/0.99  res_backward_subsumption_resolution:    0
% 2.69/0.99  res_clause_to_clause_subsumption:       253
% 2.69/0.99  res_orphan_elimination:                 0
% 2.69/0.99  res_tautology_del:                      53
% 2.69/0.99  res_num_eq_res_simplified:              0
% 2.69/0.99  res_num_sel_changes:                    0
% 2.69/0.99  res_moves_from_active_to_pass:          0
% 2.69/0.99  
% 2.69/0.99  ------ Superposition
% 2.69/0.99  
% 2.69/0.99  sup_time_total:                         0.
% 2.69/0.99  sup_time_generating:                    0.
% 2.69/0.99  sup_time_sim_full:                      0.
% 2.69/0.99  sup_time_sim_immed:                     0.
% 2.69/0.99  
% 2.69/0.99  sup_num_of_clauses:                     84
% 2.69/0.99  sup_num_in_active:                      65
% 2.69/0.99  sup_num_in_passive:                     19
% 2.69/0.99  sup_num_of_loops:                       65
% 2.69/0.99  sup_fw_superposition:                   55
% 2.69/0.99  sup_bw_superposition:                   25
% 2.69/0.99  sup_immediate_simplified:               10
% 2.69/0.99  sup_given_eliminated:                   0
% 2.69/0.99  comparisons_done:                       0
% 2.69/0.99  comparisons_avoided:                    0
% 2.69/0.99  
% 2.69/0.99  ------ Simplifications
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  sim_fw_subset_subsumed:                 1
% 2.69/0.99  sim_bw_subset_subsumed:                 0
% 2.69/0.99  sim_fw_subsumed:                        2
% 2.69/0.99  sim_bw_subsumed:                        0
% 2.69/0.99  sim_fw_subsumption_res:                 0
% 2.69/0.99  sim_bw_subsumption_res:                 0
% 2.69/0.99  sim_tautology_del:                      3
% 2.69/0.99  sim_eq_tautology_del:                   0
% 2.69/0.99  sim_eq_res_simp:                        0
% 2.69/0.99  sim_fw_demodulated:                     3
% 2.69/0.99  sim_bw_demodulated:                     1
% 2.69/0.99  sim_light_normalised:                   5
% 2.69/0.99  sim_joinable_taut:                      0
% 2.69/0.99  sim_joinable_simp:                      0
% 2.69/0.99  sim_ac_normalised:                      0
% 2.69/0.99  sim_smt_subsumption:                    0
% 2.69/0.99  
%------------------------------------------------------------------------------
