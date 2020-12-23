%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:22 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 331 expanded)
%              Number of clauses        :   76 ( 136 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  305 ( 725 expanded)
%              Number of equality atoms :  122 ( 270 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f72,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f70,f70])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f61,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f73,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f41,plain,
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

fof(f42,plain,
    ( ( k2_relset_1(sK0,sK1,sK2) != sK1
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_15,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1256,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1258,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3101,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_1256,c_1258])).

cnf(c_16,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1631,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_16,c_11])).

cnf(c_5528,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_3101,c_1631])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1259,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3536,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1256,c_1259])).

cnf(c_9660,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_5528,c_3536])).

cnf(c_9663,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_9660])).

cnf(c_9669,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_9663,c_9660])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_293,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_5])).

cnf(c_1246,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_1624,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_1246])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1257,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3712,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1257])).

cnf(c_40,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4640,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3712,c_40])).

cnf(c_4641,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4640])).

cnf(c_4652,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k6_relat_1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_4641])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1392,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1393,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_178,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_178])).

cnf(c_1399,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_1885,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_1886,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1946,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1947,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1946])).

cnf(c_5914,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4652,c_24,c_1393,c_1886,c_1947])).

cnf(c_6345,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_5914,c_3536])).

cnf(c_6369,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_6345,c_11])).

cnf(c_10847,plain,
    ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_9669,c_6369])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1251,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_136,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_3,c_1])).

cnf(c_137,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_1248,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_3368,plain,
    ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1248])).

cnf(c_4434,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_3368])).

cnf(c_4767,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4434,c_24,c_1393,c_1886,c_1947])).

cnf(c_4772,plain,
    ( k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k6_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_4767,c_4641])).

cnf(c_6346,plain,
    ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_4772,c_3536])).

cnf(c_6366,plain,
    ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_6346,c_11])).

cnf(c_10849,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_10847,c_6366])).

cnf(c_793,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2084,plain,
    ( k2_relat_1(sK2) != X0
    | sK1 != X0
    | sK1 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_2085,plain,
    ( k2_relat_1(sK2) != sK1
    | sK1 = k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_1613,plain,
    ( k2_relset_1(sK0,sK1,sK2) != X0
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1928,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_20,plain,
    ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1514,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | r1_tarski(sK1,k1_relset_1(X0,X1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1564,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1493,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_792,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_819,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10849,c_2085,c_1928,c_1564,c_1493,c_819,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.46/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.02  
% 3.46/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/1.02  
% 3.46/1.02  ------  iProver source info
% 3.46/1.02  
% 3.46/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.46/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/1.02  git: non_committed_changes: false
% 3.46/1.02  git: last_make_outside_of_git: false
% 3.46/1.02  
% 3.46/1.02  ------ 
% 3.46/1.02  
% 3.46/1.02  ------ Input Options
% 3.46/1.02  
% 3.46/1.02  --out_options                           all
% 3.46/1.02  --tptp_safe_out                         true
% 3.46/1.02  --problem_path                          ""
% 3.46/1.02  --include_path                          ""
% 3.46/1.02  --clausifier                            res/vclausify_rel
% 3.46/1.02  --clausifier_options                    --mode clausify
% 3.46/1.02  --stdin                                 false
% 3.46/1.02  --stats_out                             all
% 3.46/1.02  
% 3.46/1.02  ------ General Options
% 3.46/1.02  
% 3.46/1.02  --fof                                   false
% 3.46/1.02  --time_out_real                         305.
% 3.46/1.02  --time_out_virtual                      -1.
% 3.46/1.02  --symbol_type_check                     false
% 3.46/1.02  --clausify_out                          false
% 3.46/1.02  --sig_cnt_out                           false
% 3.46/1.02  --trig_cnt_out                          false
% 3.46/1.02  --trig_cnt_out_tolerance                1.
% 3.46/1.02  --trig_cnt_out_sk_spl                   false
% 3.46/1.02  --abstr_cl_out                          false
% 3.46/1.02  
% 3.46/1.02  ------ Global Options
% 3.46/1.02  
% 3.46/1.02  --schedule                              default
% 3.46/1.02  --add_important_lit                     false
% 3.46/1.02  --prop_solver_per_cl                    1000
% 3.46/1.02  --min_unsat_core                        false
% 3.46/1.02  --soft_assumptions                      false
% 3.46/1.02  --soft_lemma_size                       3
% 3.46/1.02  --prop_impl_unit_size                   0
% 3.46/1.02  --prop_impl_unit                        []
% 3.46/1.02  --share_sel_clauses                     true
% 3.46/1.02  --reset_solvers                         false
% 3.46/1.02  --bc_imp_inh                            [conj_cone]
% 3.46/1.02  --conj_cone_tolerance                   3.
% 3.46/1.02  --extra_neg_conj                        none
% 3.46/1.02  --large_theory_mode                     true
% 3.46/1.02  --prolific_symb_bound                   200
% 3.46/1.02  --lt_threshold                          2000
% 3.46/1.02  --clause_weak_htbl                      true
% 3.46/1.02  --gc_record_bc_elim                     false
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing Options
% 3.46/1.02  
% 3.46/1.02  --preprocessing_flag                    true
% 3.46/1.02  --time_out_prep_mult                    0.1
% 3.46/1.02  --splitting_mode                        input
% 3.46/1.02  --splitting_grd                         true
% 3.46/1.02  --splitting_cvd                         false
% 3.46/1.02  --splitting_cvd_svl                     false
% 3.46/1.02  --splitting_nvd                         32
% 3.46/1.02  --sub_typing                            true
% 3.46/1.02  --prep_gs_sim                           true
% 3.46/1.02  --prep_unflatten                        true
% 3.46/1.02  --prep_res_sim                          true
% 3.46/1.02  --prep_upred                            true
% 3.46/1.02  --prep_sem_filter                       exhaustive
% 3.46/1.02  --prep_sem_filter_out                   false
% 3.46/1.02  --pred_elim                             true
% 3.46/1.02  --res_sim_input                         true
% 3.46/1.02  --eq_ax_congr_red                       true
% 3.46/1.02  --pure_diseq_elim                       true
% 3.46/1.02  --brand_transform                       false
% 3.46/1.02  --non_eq_to_eq                          false
% 3.46/1.02  --prep_def_merge                        true
% 3.46/1.02  --prep_def_merge_prop_impl              false
% 3.46/1.02  --prep_def_merge_mbd                    true
% 3.46/1.02  --prep_def_merge_tr_red                 false
% 3.46/1.02  --prep_def_merge_tr_cl                  false
% 3.46/1.02  --smt_preprocessing                     true
% 3.46/1.02  --smt_ac_axioms                         fast
% 3.46/1.02  --preprocessed_out                      false
% 3.46/1.02  --preprocessed_stats                    false
% 3.46/1.02  
% 3.46/1.02  ------ Abstraction refinement Options
% 3.46/1.02  
% 3.46/1.02  --abstr_ref                             []
% 3.46/1.02  --abstr_ref_prep                        false
% 3.46/1.02  --abstr_ref_until_sat                   false
% 3.46/1.02  --abstr_ref_sig_restrict                funpre
% 3.46/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/1.02  --abstr_ref_under                       []
% 3.46/1.02  
% 3.46/1.02  ------ SAT Options
% 3.46/1.02  
% 3.46/1.02  --sat_mode                              false
% 3.46/1.02  --sat_fm_restart_options                ""
% 3.46/1.02  --sat_gr_def                            false
% 3.46/1.02  --sat_epr_types                         true
% 3.46/1.02  --sat_non_cyclic_types                  false
% 3.46/1.02  --sat_finite_models                     false
% 3.46/1.02  --sat_fm_lemmas                         false
% 3.46/1.02  --sat_fm_prep                           false
% 3.46/1.02  --sat_fm_uc_incr                        true
% 3.46/1.02  --sat_out_model                         small
% 3.46/1.02  --sat_out_clauses                       false
% 3.46/1.02  
% 3.46/1.02  ------ QBF Options
% 3.46/1.02  
% 3.46/1.02  --qbf_mode                              false
% 3.46/1.02  --qbf_elim_univ                         false
% 3.46/1.02  --qbf_dom_inst                          none
% 3.46/1.02  --qbf_dom_pre_inst                      false
% 3.46/1.02  --qbf_sk_in                             false
% 3.46/1.02  --qbf_pred_elim                         true
% 3.46/1.02  --qbf_split                             512
% 3.46/1.02  
% 3.46/1.02  ------ BMC1 Options
% 3.46/1.02  
% 3.46/1.02  --bmc1_incremental                      false
% 3.46/1.02  --bmc1_axioms                           reachable_all
% 3.46/1.02  --bmc1_min_bound                        0
% 3.46/1.02  --bmc1_max_bound                        -1
% 3.46/1.02  --bmc1_max_bound_default                -1
% 3.46/1.02  --bmc1_symbol_reachability              true
% 3.46/1.02  --bmc1_property_lemmas                  false
% 3.46/1.02  --bmc1_k_induction                      false
% 3.46/1.02  --bmc1_non_equiv_states                 false
% 3.46/1.02  --bmc1_deadlock                         false
% 3.46/1.02  --bmc1_ucm                              false
% 3.46/1.02  --bmc1_add_unsat_core                   none
% 3.46/1.02  --bmc1_unsat_core_children              false
% 3.46/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/1.02  --bmc1_out_stat                         full
% 3.46/1.02  --bmc1_ground_init                      false
% 3.46/1.02  --bmc1_pre_inst_next_state              false
% 3.46/1.02  --bmc1_pre_inst_state                   false
% 3.46/1.02  --bmc1_pre_inst_reach_state             false
% 3.46/1.02  --bmc1_out_unsat_core                   false
% 3.46/1.02  --bmc1_aig_witness_out                  false
% 3.46/1.02  --bmc1_verbose                          false
% 3.46/1.02  --bmc1_dump_clauses_tptp                false
% 3.46/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.46/1.02  --bmc1_dump_file                        -
% 3.46/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.46/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.46/1.02  --bmc1_ucm_extend_mode                  1
% 3.46/1.02  --bmc1_ucm_init_mode                    2
% 3.46/1.02  --bmc1_ucm_cone_mode                    none
% 3.46/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.46/1.02  --bmc1_ucm_relax_model                  4
% 3.46/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.46/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/1.02  --bmc1_ucm_layered_model                none
% 3.46/1.02  --bmc1_ucm_max_lemma_size               10
% 3.46/1.02  
% 3.46/1.02  ------ AIG Options
% 3.46/1.02  
% 3.46/1.02  --aig_mode                              false
% 3.46/1.02  
% 3.46/1.02  ------ Instantiation Options
% 3.46/1.02  
% 3.46/1.02  --instantiation_flag                    true
% 3.46/1.02  --inst_sos_flag                         false
% 3.46/1.02  --inst_sos_phase                        true
% 3.46/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/1.02  --inst_lit_sel_side                     num_symb
% 3.46/1.02  --inst_solver_per_active                1400
% 3.46/1.02  --inst_solver_calls_frac                1.
% 3.46/1.02  --inst_passive_queue_type               priority_queues
% 3.46/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/1.02  --inst_passive_queues_freq              [25;2]
% 3.46/1.02  --inst_dismatching                      true
% 3.46/1.02  --inst_eager_unprocessed_to_passive     true
% 3.46/1.02  --inst_prop_sim_given                   true
% 3.46/1.02  --inst_prop_sim_new                     false
% 3.46/1.02  --inst_subs_new                         false
% 3.46/1.02  --inst_eq_res_simp                      false
% 3.46/1.02  --inst_subs_given                       false
% 3.46/1.02  --inst_orphan_elimination               true
% 3.46/1.02  --inst_learning_loop_flag               true
% 3.46/1.02  --inst_learning_start                   3000
% 3.46/1.02  --inst_learning_factor                  2
% 3.46/1.02  --inst_start_prop_sim_after_learn       3
% 3.46/1.02  --inst_sel_renew                        solver
% 3.46/1.02  --inst_lit_activity_flag                true
% 3.46/1.02  --inst_restr_to_given                   false
% 3.46/1.02  --inst_activity_threshold               500
% 3.46/1.02  --inst_out_proof                        true
% 3.46/1.02  
% 3.46/1.02  ------ Resolution Options
% 3.46/1.02  
% 3.46/1.02  --resolution_flag                       true
% 3.46/1.02  --res_lit_sel                           adaptive
% 3.46/1.02  --res_lit_sel_side                      none
% 3.46/1.02  --res_ordering                          kbo
% 3.46/1.02  --res_to_prop_solver                    active
% 3.46/1.02  --res_prop_simpl_new                    false
% 3.46/1.02  --res_prop_simpl_given                  true
% 3.46/1.02  --res_passive_queue_type                priority_queues
% 3.46/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/1.02  --res_passive_queues_freq               [15;5]
% 3.46/1.02  --res_forward_subs                      full
% 3.46/1.02  --res_backward_subs                     full
% 3.46/1.02  --res_forward_subs_resolution           true
% 3.46/1.02  --res_backward_subs_resolution          true
% 3.46/1.02  --res_orphan_elimination                true
% 3.46/1.02  --res_time_limit                        2.
% 3.46/1.02  --res_out_proof                         true
% 3.46/1.02  
% 3.46/1.02  ------ Superposition Options
% 3.46/1.02  
% 3.46/1.02  --superposition_flag                    true
% 3.46/1.02  --sup_passive_queue_type                priority_queues
% 3.46/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.46/1.02  --demod_completeness_check              fast
% 3.46/1.02  --demod_use_ground                      true
% 3.46/1.02  --sup_to_prop_solver                    passive
% 3.46/1.02  --sup_prop_simpl_new                    true
% 3.46/1.02  --sup_prop_simpl_given                  true
% 3.46/1.02  --sup_fun_splitting                     false
% 3.46/1.02  --sup_smt_interval                      50000
% 3.46/1.02  
% 3.46/1.02  ------ Superposition Simplification Setup
% 3.46/1.02  
% 3.46/1.02  --sup_indices_passive                   []
% 3.46/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/1.02  --sup_full_bw                           [BwDemod]
% 3.46/1.02  --sup_immed_triv                        [TrivRules]
% 3.46/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/1.02  --sup_immed_bw_main                     []
% 3.46/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/1.02  
% 3.46/1.02  ------ Combination Options
% 3.46/1.02  
% 3.46/1.02  --comb_res_mult                         3
% 3.46/1.02  --comb_sup_mult                         2
% 3.46/1.02  --comb_inst_mult                        10
% 3.46/1.02  
% 3.46/1.02  ------ Debug Options
% 3.46/1.02  
% 3.46/1.02  --dbg_backtrace                         false
% 3.46/1.02  --dbg_dump_prop_clauses                 false
% 3.46/1.02  --dbg_dump_prop_clauses_file            -
% 3.46/1.02  --dbg_out_stat                          false
% 3.46/1.02  ------ Parsing...
% 3.46/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.02  ------ Proving...
% 3.46/1.02  ------ Problem Properties 
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  clauses                                 22
% 3.46/1.02  conjectures                             3
% 3.46/1.02  EPR                                     1
% 3.46/1.02  Horn                                    22
% 3.46/1.02  unary                                   8
% 3.46/1.02  binary                                  7
% 3.46/1.02  lits                                    43
% 3.46/1.02  lits eq                                 10
% 3.46/1.02  fd_pure                                 0
% 3.46/1.02  fd_pseudo                               0
% 3.46/1.02  fd_cond                                 0
% 3.46/1.02  fd_pseudo_cond                          0
% 3.46/1.02  AC symbols                              0
% 3.46/1.02  
% 3.46/1.02  ------ Schedule dynamic 5 is on 
% 3.46/1.02  
% 3.46/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ 
% 3.46/1.02  Current options:
% 3.46/1.02  ------ 
% 3.46/1.02  
% 3.46/1.02  ------ Input Options
% 3.46/1.02  
% 3.46/1.02  --out_options                           all
% 3.46/1.02  --tptp_safe_out                         true
% 3.46/1.02  --problem_path                          ""
% 3.46/1.02  --include_path                          ""
% 3.46/1.02  --clausifier                            res/vclausify_rel
% 3.46/1.02  --clausifier_options                    --mode clausify
% 3.46/1.02  --stdin                                 false
% 3.46/1.02  --stats_out                             all
% 3.46/1.02  
% 3.46/1.02  ------ General Options
% 3.46/1.02  
% 3.46/1.02  --fof                                   false
% 3.46/1.02  --time_out_real                         305.
% 3.46/1.02  --time_out_virtual                      -1.
% 3.46/1.02  --symbol_type_check                     false
% 3.46/1.02  --clausify_out                          false
% 3.46/1.02  --sig_cnt_out                           false
% 3.46/1.02  --trig_cnt_out                          false
% 3.46/1.02  --trig_cnt_out_tolerance                1.
% 3.46/1.02  --trig_cnt_out_sk_spl                   false
% 3.46/1.02  --abstr_cl_out                          false
% 3.46/1.02  
% 3.46/1.02  ------ Global Options
% 3.46/1.02  
% 3.46/1.02  --schedule                              default
% 3.46/1.02  --add_important_lit                     false
% 3.46/1.02  --prop_solver_per_cl                    1000
% 3.46/1.02  --min_unsat_core                        false
% 3.46/1.02  --soft_assumptions                      false
% 3.46/1.02  --soft_lemma_size                       3
% 3.46/1.02  --prop_impl_unit_size                   0
% 3.46/1.02  --prop_impl_unit                        []
% 3.46/1.02  --share_sel_clauses                     true
% 3.46/1.02  --reset_solvers                         false
% 3.46/1.02  --bc_imp_inh                            [conj_cone]
% 3.46/1.02  --conj_cone_tolerance                   3.
% 3.46/1.02  --extra_neg_conj                        none
% 3.46/1.02  --large_theory_mode                     true
% 3.46/1.02  --prolific_symb_bound                   200
% 3.46/1.02  --lt_threshold                          2000
% 3.46/1.02  --clause_weak_htbl                      true
% 3.46/1.02  --gc_record_bc_elim                     false
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing Options
% 3.46/1.02  
% 3.46/1.02  --preprocessing_flag                    true
% 3.46/1.02  --time_out_prep_mult                    0.1
% 3.46/1.02  --splitting_mode                        input
% 3.46/1.02  --splitting_grd                         true
% 3.46/1.02  --splitting_cvd                         false
% 3.46/1.02  --splitting_cvd_svl                     false
% 3.46/1.02  --splitting_nvd                         32
% 3.46/1.02  --sub_typing                            true
% 3.46/1.02  --prep_gs_sim                           true
% 3.46/1.02  --prep_unflatten                        true
% 3.46/1.02  --prep_res_sim                          true
% 3.46/1.02  --prep_upred                            true
% 3.46/1.02  --prep_sem_filter                       exhaustive
% 3.46/1.02  --prep_sem_filter_out                   false
% 3.46/1.02  --pred_elim                             true
% 3.46/1.02  --res_sim_input                         true
% 3.46/1.02  --eq_ax_congr_red                       true
% 3.46/1.02  --pure_diseq_elim                       true
% 3.46/1.02  --brand_transform                       false
% 3.46/1.02  --non_eq_to_eq                          false
% 3.46/1.02  --prep_def_merge                        true
% 3.46/1.02  --prep_def_merge_prop_impl              false
% 3.46/1.02  --prep_def_merge_mbd                    true
% 3.46/1.02  --prep_def_merge_tr_red                 false
% 3.46/1.02  --prep_def_merge_tr_cl                  false
% 3.46/1.02  --smt_preprocessing                     true
% 3.46/1.02  --smt_ac_axioms                         fast
% 3.46/1.02  --preprocessed_out                      false
% 3.46/1.02  --preprocessed_stats                    false
% 3.46/1.02  
% 3.46/1.02  ------ Abstraction refinement Options
% 3.46/1.02  
% 3.46/1.02  --abstr_ref                             []
% 3.46/1.02  --abstr_ref_prep                        false
% 3.46/1.02  --abstr_ref_until_sat                   false
% 3.46/1.02  --abstr_ref_sig_restrict                funpre
% 3.46/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/1.02  --abstr_ref_under                       []
% 3.46/1.02  
% 3.46/1.02  ------ SAT Options
% 3.46/1.02  
% 3.46/1.02  --sat_mode                              false
% 3.46/1.02  --sat_fm_restart_options                ""
% 3.46/1.02  --sat_gr_def                            false
% 3.46/1.02  --sat_epr_types                         true
% 3.46/1.02  --sat_non_cyclic_types                  false
% 3.46/1.02  --sat_finite_models                     false
% 3.46/1.02  --sat_fm_lemmas                         false
% 3.46/1.02  --sat_fm_prep                           false
% 3.46/1.02  --sat_fm_uc_incr                        true
% 3.46/1.02  --sat_out_model                         small
% 3.46/1.02  --sat_out_clauses                       false
% 3.46/1.02  
% 3.46/1.02  ------ QBF Options
% 3.46/1.02  
% 3.46/1.02  --qbf_mode                              false
% 3.46/1.02  --qbf_elim_univ                         false
% 3.46/1.02  --qbf_dom_inst                          none
% 3.46/1.02  --qbf_dom_pre_inst                      false
% 3.46/1.02  --qbf_sk_in                             false
% 3.46/1.02  --qbf_pred_elim                         true
% 3.46/1.02  --qbf_split                             512
% 3.46/1.02  
% 3.46/1.02  ------ BMC1 Options
% 3.46/1.02  
% 3.46/1.02  --bmc1_incremental                      false
% 3.46/1.02  --bmc1_axioms                           reachable_all
% 3.46/1.02  --bmc1_min_bound                        0
% 3.46/1.02  --bmc1_max_bound                        -1
% 3.46/1.02  --bmc1_max_bound_default                -1
% 3.46/1.02  --bmc1_symbol_reachability              true
% 3.46/1.02  --bmc1_property_lemmas                  false
% 3.46/1.02  --bmc1_k_induction                      false
% 3.46/1.02  --bmc1_non_equiv_states                 false
% 3.46/1.02  --bmc1_deadlock                         false
% 3.46/1.02  --bmc1_ucm                              false
% 3.46/1.02  --bmc1_add_unsat_core                   none
% 3.46/1.02  --bmc1_unsat_core_children              false
% 3.46/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/1.02  --bmc1_out_stat                         full
% 3.46/1.02  --bmc1_ground_init                      false
% 3.46/1.02  --bmc1_pre_inst_next_state              false
% 3.46/1.02  --bmc1_pre_inst_state                   false
% 3.46/1.02  --bmc1_pre_inst_reach_state             false
% 3.46/1.02  --bmc1_out_unsat_core                   false
% 3.46/1.02  --bmc1_aig_witness_out                  false
% 3.46/1.02  --bmc1_verbose                          false
% 3.46/1.02  --bmc1_dump_clauses_tptp                false
% 3.46/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.46/1.02  --bmc1_dump_file                        -
% 3.46/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.46/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.46/1.02  --bmc1_ucm_extend_mode                  1
% 3.46/1.02  --bmc1_ucm_init_mode                    2
% 3.46/1.02  --bmc1_ucm_cone_mode                    none
% 3.46/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.46/1.02  --bmc1_ucm_relax_model                  4
% 3.46/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.46/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/1.02  --bmc1_ucm_layered_model                none
% 3.46/1.02  --bmc1_ucm_max_lemma_size               10
% 3.46/1.02  
% 3.46/1.02  ------ AIG Options
% 3.46/1.02  
% 3.46/1.02  --aig_mode                              false
% 3.46/1.02  
% 3.46/1.02  ------ Instantiation Options
% 3.46/1.02  
% 3.46/1.02  --instantiation_flag                    true
% 3.46/1.02  --inst_sos_flag                         false
% 3.46/1.02  --inst_sos_phase                        true
% 3.46/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/1.02  --inst_lit_sel_side                     none
% 3.46/1.02  --inst_solver_per_active                1400
% 3.46/1.02  --inst_solver_calls_frac                1.
% 3.46/1.02  --inst_passive_queue_type               priority_queues
% 3.46/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/1.02  --inst_passive_queues_freq              [25;2]
% 3.46/1.02  --inst_dismatching                      true
% 3.46/1.02  --inst_eager_unprocessed_to_passive     true
% 3.46/1.02  --inst_prop_sim_given                   true
% 3.46/1.02  --inst_prop_sim_new                     false
% 3.46/1.02  --inst_subs_new                         false
% 3.46/1.02  --inst_eq_res_simp                      false
% 3.46/1.02  --inst_subs_given                       false
% 3.46/1.02  --inst_orphan_elimination               true
% 3.46/1.02  --inst_learning_loop_flag               true
% 3.46/1.02  --inst_learning_start                   3000
% 3.46/1.02  --inst_learning_factor                  2
% 3.46/1.02  --inst_start_prop_sim_after_learn       3
% 3.46/1.02  --inst_sel_renew                        solver
% 3.46/1.02  --inst_lit_activity_flag                true
% 3.46/1.02  --inst_restr_to_given                   false
% 3.46/1.02  --inst_activity_threshold               500
% 3.46/1.02  --inst_out_proof                        true
% 3.46/1.02  
% 3.46/1.02  ------ Resolution Options
% 3.46/1.02  
% 3.46/1.02  --resolution_flag                       false
% 3.46/1.02  --res_lit_sel                           adaptive
% 3.46/1.02  --res_lit_sel_side                      none
% 3.46/1.02  --res_ordering                          kbo
% 3.46/1.02  --res_to_prop_solver                    active
% 3.46/1.02  --res_prop_simpl_new                    false
% 3.46/1.02  --res_prop_simpl_given                  true
% 3.46/1.02  --res_passive_queue_type                priority_queues
% 3.46/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/1.02  --res_passive_queues_freq               [15;5]
% 3.46/1.02  --res_forward_subs                      full
% 3.46/1.02  --res_backward_subs                     full
% 3.46/1.02  --res_forward_subs_resolution           true
% 3.46/1.02  --res_backward_subs_resolution          true
% 3.46/1.02  --res_orphan_elimination                true
% 3.46/1.02  --res_time_limit                        2.
% 3.46/1.02  --res_out_proof                         true
% 3.46/1.02  
% 3.46/1.02  ------ Superposition Options
% 3.46/1.02  
% 3.46/1.02  --superposition_flag                    true
% 3.46/1.02  --sup_passive_queue_type                priority_queues
% 3.46/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.46/1.02  --demod_completeness_check              fast
% 3.46/1.02  --demod_use_ground                      true
% 3.46/1.02  --sup_to_prop_solver                    passive
% 3.46/1.02  --sup_prop_simpl_new                    true
% 3.46/1.02  --sup_prop_simpl_given                  true
% 3.46/1.02  --sup_fun_splitting                     false
% 3.46/1.02  --sup_smt_interval                      50000
% 3.46/1.02  
% 3.46/1.02  ------ Superposition Simplification Setup
% 3.46/1.02  
% 3.46/1.02  --sup_indices_passive                   []
% 3.46/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/1.02  --sup_full_bw                           [BwDemod]
% 3.46/1.02  --sup_immed_triv                        [TrivRules]
% 3.46/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/1.02  --sup_immed_bw_main                     []
% 3.46/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/1.02  
% 3.46/1.02  ------ Combination Options
% 3.46/1.02  
% 3.46/1.02  --comb_res_mult                         3
% 3.46/1.02  --comb_sup_mult                         2
% 3.46/1.02  --comb_inst_mult                        10
% 3.46/1.02  
% 3.46/1.02  ------ Debug Options
% 3.46/1.02  
% 3.46/1.02  --dbg_backtrace                         false
% 3.46/1.02  --dbg_dump_prop_clauses                 false
% 3.46/1.02  --dbg_dump_prop_clauses_file            -
% 3.46/1.02  --dbg_out_stat                          false
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ Proving...
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  % SZS status Theorem for theBenchmark.p
% 3.46/1.02  
% 3.46/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/1.02  
% 3.46/1.02  fof(f1,axiom,(
% 3.46/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f43,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f1])).
% 3.46/1.02  
% 3.46/1.02  fof(f2,axiom,(
% 3.46/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f44,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f2])).
% 3.46/1.02  
% 3.46/1.02  fof(f3,axiom,(
% 3.46/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f45,plain,(
% 3.46/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f3])).
% 3.46/1.02  
% 3.46/1.02  fof(f70,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.46/1.02    inference(definition_unfolding,[],[f44,f45])).
% 3.46/1.02  
% 3.46/1.02  fof(f72,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.46/1.02    inference(definition_unfolding,[],[f43,f70,f70])).
% 3.46/1.02  
% 3.46/1.02  fof(f15,axiom,(
% 3.46/1.02    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f23,plain,(
% 3.46/1.02    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.46/1.02    inference(pure_predicate_removal,[],[f15])).
% 3.46/1.02  
% 3.46/1.02  fof(f61,plain,(
% 3.46/1.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f23])).
% 3.46/1.02  
% 3.46/1.02  fof(f13,axiom,(
% 3.46/1.02    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f30,plain,(
% 3.46/1.02    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.46/1.02    inference(ennf_transformation,[],[f13])).
% 3.46/1.02  
% 3.46/1.02  fof(f59,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f30])).
% 3.46/1.02  
% 3.46/1.02  fof(f16,axiom,(
% 3.46/1.02    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f62,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f16])).
% 3.46/1.02  
% 3.46/1.02  fof(f4,axiom,(
% 3.46/1.02    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f46,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f4])).
% 3.46/1.02  
% 3.46/1.02  fof(f71,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.46/1.02    inference(definition_unfolding,[],[f46,f70])).
% 3.46/1.02  
% 3.46/1.02  fof(f73,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 3.46/1.02    inference(definition_unfolding,[],[f62,f71])).
% 3.46/1.02  
% 3.46/1.02  fof(f12,axiom,(
% 3.46/1.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f58,plain,(
% 3.46/1.02    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.46/1.02    inference(cnf_transformation,[],[f12])).
% 3.46/1.02  
% 3.46/1.02  fof(f10,axiom,(
% 3.46/1.02    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f27,plain,(
% 3.46/1.02    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.46/1.02    inference(ennf_transformation,[],[f10])).
% 3.46/1.02  
% 3.46/1.02  fof(f54,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f27])).
% 3.46/1.02  
% 3.46/1.02  fof(f20,conjecture,(
% 3.46/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f21,negated_conjecture,(
% 3.46/1.02    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 3.46/1.02    inference(negated_conjecture,[],[f20])).
% 3.46/1.02  
% 3.46/1.02  fof(f37,plain,(
% 3.46/1.02    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/1.02    inference(ennf_transformation,[],[f21])).
% 3.46/1.02  
% 3.46/1.02  fof(f38,plain,(
% 3.46/1.02    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/1.02    inference(flattening,[],[f37])).
% 3.46/1.02  
% 3.46/1.02  fof(f41,plain,(
% 3.46/1.02    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 3.46/1.02    introduced(choice_axiom,[])).
% 3.46/1.02  
% 3.46/1.02  fof(f42,plain,(
% 3.46/1.02    (k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.46/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41])).
% 3.46/1.02  
% 3.46/1.02  fof(f67,plain,(
% 3.46/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.46/1.02    inference(cnf_transformation,[],[f42])).
% 3.46/1.02  
% 3.46/1.02  fof(f17,axiom,(
% 3.46/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f22,plain,(
% 3.46/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.46/1.02    inference(pure_predicate_removal,[],[f17])).
% 3.46/1.02  
% 3.46/1.02  fof(f33,plain,(
% 3.46/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/1.02    inference(ennf_transformation,[],[f22])).
% 3.46/1.02  
% 3.46/1.02  fof(f63,plain,(
% 3.46/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f33])).
% 3.46/1.02  
% 3.46/1.02  fof(f7,axiom,(
% 3.46/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f25,plain,(
% 3.46/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.46/1.02    inference(ennf_transformation,[],[f7])).
% 3.46/1.02  
% 3.46/1.02  fof(f40,plain,(
% 3.46/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.46/1.02    inference(nnf_transformation,[],[f25])).
% 3.46/1.02  
% 3.46/1.02  fof(f50,plain,(
% 3.46/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f40])).
% 3.46/1.02  
% 3.46/1.02  fof(f57,plain,(
% 3.46/1.02    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.46/1.02    inference(cnf_transformation,[],[f12])).
% 3.46/1.02  
% 3.46/1.02  fof(f14,axiom,(
% 3.46/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f31,plain,(
% 3.46/1.02    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.46/1.02    inference(ennf_transformation,[],[f14])).
% 3.46/1.02  
% 3.46/1.02  fof(f32,plain,(
% 3.46/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.46/1.02    inference(flattening,[],[f31])).
% 3.46/1.02  
% 3.46/1.02  fof(f60,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f32])).
% 3.46/1.02  
% 3.46/1.02  fof(f5,axiom,(
% 3.46/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f39,plain,(
% 3.46/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.46/1.02    inference(nnf_transformation,[],[f5])).
% 3.46/1.02  
% 3.46/1.02  fof(f47,plain,(
% 3.46/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f39])).
% 3.46/1.02  
% 3.46/1.02  fof(f6,axiom,(
% 3.46/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f24,plain,(
% 3.46/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.46/1.02    inference(ennf_transformation,[],[f6])).
% 3.46/1.02  
% 3.46/1.02  fof(f49,plain,(
% 3.46/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f24])).
% 3.46/1.02  
% 3.46/1.02  fof(f48,plain,(
% 3.46/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f39])).
% 3.46/1.02  
% 3.46/1.02  fof(f8,axiom,(
% 3.46/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f52,plain,(
% 3.46/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f8])).
% 3.46/1.02  
% 3.46/1.02  fof(f68,plain,(
% 3.46/1.02    r1_tarski(k6_relat_1(sK1),sK2)),
% 3.46/1.02    inference(cnf_transformation,[],[f42])).
% 3.46/1.02  
% 3.46/1.02  fof(f11,axiom,(
% 3.46/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f28,plain,(
% 3.46/1.02    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.46/1.02    inference(ennf_transformation,[],[f11])).
% 3.46/1.02  
% 3.46/1.02  fof(f29,plain,(
% 3.46/1.02    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.46/1.02    inference(flattening,[],[f28])).
% 3.46/1.02  
% 3.46/1.02  fof(f56,plain,(
% 3.46/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f29])).
% 3.46/1.02  
% 3.46/1.02  fof(f19,axiom,(
% 3.46/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f35,plain,(
% 3.46/1.02    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/1.02    inference(ennf_transformation,[],[f19])).
% 3.46/1.02  
% 3.46/1.02  fof(f36,plain,(
% 3.46/1.02    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/1.02    inference(flattening,[],[f35])).
% 3.46/1.02  
% 3.46/1.02  fof(f65,plain,(
% 3.46/1.02    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f36])).
% 3.46/1.02  
% 3.46/1.02  fof(f18,axiom,(
% 3.46/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f34,plain,(
% 3.46/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/1.02    inference(ennf_transformation,[],[f18])).
% 3.46/1.02  
% 3.46/1.02  fof(f64,plain,(
% 3.46/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f34])).
% 3.46/1.02  
% 3.46/1.02  fof(f69,plain,(
% 3.46/1.02    k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 3.46/1.02    inference(cnf_transformation,[],[f42])).
% 3.46/1.02  
% 3.46/1.02  cnf(c_0,plain,
% 3.46/1.02      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.46/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_15,plain,
% 3.46/1.02      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.46/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1256,plain,
% 3.46/1.02      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_13,plain,
% 3.46/1.02      ( ~ v1_relat_1(X0)
% 3.46/1.02      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.46/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1258,plain,
% 3.46/1.02      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.46/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_3101,plain,
% 3.46/1.02      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_1256,c_1258]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_16,plain,
% 3.46/1.02      ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 3.46/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_11,plain,
% 3.46/1.02      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.46/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1631,plain,
% 3.46/1.02      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_16,c_11]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_5528,plain,
% 3.46/1.02      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.46/1.02      inference(demodulation,[status(thm)],[c_3101,c_1631]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_8,plain,
% 3.46/1.02      ( ~ v1_relat_1(X0)
% 3.46/1.02      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.46/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1259,plain,
% 3.46/1.02      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.46/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_3536,plain,
% 3.46/1.02      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_1256,c_1259]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_9660,plain,
% 3.46/1.02      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.46/1.02      inference(light_normalisation,[status(thm)],[c_5528,c_3536]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_9663,plain,
% 3.46/1.02      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_0,c_9660]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_9669,plain,
% 3.46/1.02      ( k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_9663,c_9660]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_23,negated_conjecture,
% 3.46/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.46/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1250,plain,
% 3.46/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_17,plain,
% 3.46/1.02      ( v5_relat_1(X0,X1)
% 3.46/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.46/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_5,plain,
% 3.46/1.02      ( ~ v5_relat_1(X0,X1)
% 3.46/1.02      | r1_tarski(k2_relat_1(X0),X1)
% 3.46/1.02      | ~ v1_relat_1(X0) ),
% 3.46/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_293,plain,
% 3.46/1.02      ( r1_tarski(k2_relat_1(X0),X1)
% 3.46/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.46/1.02      | ~ v1_relat_1(X0) ),
% 3.46/1.02      inference(resolution,[status(thm)],[c_17,c_5]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1246,plain,
% 3.46/1.02      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.46/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.46/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1624,plain,
% 3.46/1.02      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 3.46/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_1250,c_1246]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_12,plain,
% 3.46/1.02      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.46/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_14,plain,
% 3.46/1.02      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.46/1.02      | ~ v1_relat_1(X0)
% 3.46/1.02      | k7_relat_1(X0,X1) = X0 ),
% 3.46/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1257,plain,
% 3.46/1.02      ( k7_relat_1(X0,X1) = X0
% 3.46/1.02      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.46/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_3712,plain,
% 3.46/1.02      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.46/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.46/1.02      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_12,c_1257]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_40,plain,
% 3.46/1.02      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_4640,plain,
% 3.46/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.46/1.02      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 3.46/1.02      inference(global_propositional_subsumption,
% 3.46/1.02                [status(thm)],
% 3.46/1.02                [c_3712,c_40]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_4641,plain,
% 3.46/1.02      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.46/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 3.46/1.02      inference(renaming,[status(thm)],[c_4640]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_4652,plain,
% 3.46/1.02      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k6_relat_1(k2_relat_1(sK2))
% 3.46/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_1624,c_4641]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_24,plain,
% 3.46/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_2,plain,
% 3.46/1.02      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.46/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1392,plain,
% 3.46/1.02      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 3.46/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1393,plain,
% 3.46/1.02      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.46/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_3,plain,
% 3.46/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.46/1.02      | ~ v1_relat_1(X1)
% 3.46/1.02      | v1_relat_1(X0) ),
% 3.46/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1,plain,
% 3.46/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.46/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_178,plain,
% 3.46/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.46/1.02      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_217,plain,
% 3.46/1.02      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.46/1.02      inference(bin_hyper_res,[status(thm)],[c_3,c_178]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1399,plain,
% 3.46/1.02      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.46/1.02      | v1_relat_1(X0)
% 3.46/1.02      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_217]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1885,plain,
% 3.46/1.02      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 3.46/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.46/1.02      | v1_relat_1(sK2) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_1399]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1886,plain,
% 3.46/1.02      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.46/1.02      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.46/1.02      | v1_relat_1(sK2) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_6,plain,
% 3.46/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.46/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1946,plain,
% 3.46/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1947,plain,
% 3.46/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_1946]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_5914,plain,
% 3.46/1.02      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k6_relat_1(k2_relat_1(sK2)) ),
% 3.46/1.02      inference(global_propositional_subsumption,
% 3.46/1.02                [status(thm)],
% 3.46/1.02                [c_4652,c_24,c_1393,c_1886,c_1947]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_6345,plain,
% 3.46/1.02      ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_5914,c_3536]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_6369,plain,
% 3.46/1.02      ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(sK2) ),
% 3.46/1.02      inference(demodulation,[status(thm)],[c_6345,c_11]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_10847,plain,
% 3.46/1.02      ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_9669,c_6369]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_22,negated_conjecture,
% 3.46/1.02      ( r1_tarski(k6_relat_1(sK1),sK2) ),
% 3.46/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1251,plain,
% 3.46/1.02      ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_9,plain,
% 3.46/1.02      ( ~ r1_tarski(X0,X1)
% 3.46/1.02      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.46/1.02      | ~ v1_relat_1(X0)
% 3.46/1.02      | ~ v1_relat_1(X1) ),
% 3.46/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_136,plain,
% 3.46/1.02      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.46/1.02      | ~ r1_tarski(X0,X1)
% 3.46/1.02      | ~ v1_relat_1(X1) ),
% 3.46/1.02      inference(global_propositional_subsumption,
% 3.46/1.02                [status(thm)],
% 3.46/1.02                [c_9,c_3,c_1]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_137,plain,
% 3.46/1.02      ( ~ r1_tarski(X0,X1)
% 3.46/1.02      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.46/1.02      | ~ v1_relat_1(X1) ),
% 3.46/1.02      inference(renaming,[status(thm)],[c_136]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1248,plain,
% 3.46/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.46/1.02      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.46/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_3368,plain,
% 3.46/1.02      ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
% 3.46/1.02      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 3.46/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_11,c_1248]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_4434,plain,
% 3.46/1.02      ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
% 3.46/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_1251,c_3368]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_4767,plain,
% 3.46/1.02      ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top ),
% 3.46/1.02      inference(global_propositional_subsumption,
% 3.46/1.02                [status(thm)],
% 3.46/1.02                [c_4434,c_24,c_1393,c_1886,c_1947]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_4772,plain,
% 3.46/1.02      ( k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k6_relat_1(sK1) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_4767,c_4641]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_6346,plain,
% 3.46/1.02      ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k2_relat_1(k6_relat_1(sK1)) ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_4772,c_3536]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_6366,plain,
% 3.46/1.02      ( k9_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = sK1 ),
% 3.46/1.02      inference(demodulation,[status(thm)],[c_6346,c_11]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_10849,plain,
% 3.46/1.02      ( k2_relat_1(sK2) = sK1 ),
% 3.46/1.02      inference(light_normalisation,[status(thm)],[c_10847,c_6366]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_793,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_2084,plain,
% 3.46/1.02      ( k2_relat_1(sK2) != X0 | sK1 != X0 | sK1 = k2_relat_1(sK2) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_793]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_2085,plain,
% 3.46/1.02      ( k2_relat_1(sK2) != sK1 | sK1 = k2_relat_1(sK2) | sK1 != sK1 ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_2084]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1613,plain,
% 3.46/1.02      ( k2_relset_1(sK0,sK1,sK2) != X0
% 3.46/1.02      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.46/1.02      | sK1 != X0 ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_793]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1928,plain,
% 3.46/1.02      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 3.46/1.02      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.46/1.02      | sK1 != k2_relat_1(sK2) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_1613]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_20,plain,
% 3.46/1.02      ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
% 3.46/1.02      | ~ r1_tarski(k6_relat_1(X0),X3)
% 3.46/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.46/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1514,plain,
% 3.46/1.02      ( ~ r1_tarski(k6_relat_1(sK1),sK2)
% 3.46/1.02      | r1_tarski(sK1,k1_relset_1(X0,X1,sK2))
% 3.46/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_20]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1564,plain,
% 3.46/1.02      ( ~ r1_tarski(k6_relat_1(sK1),sK2)
% 3.46/1.02      | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
% 3.46/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_1514]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_18,plain,
% 3.46/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.46/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1493,plain,
% 3.46/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.46/1.02      | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_18]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_792,plain,( X0 = X0 ),theory(equality) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_819,plain,
% 3.46/1.02      ( sK1 = sK1 ),
% 3.46/1.02      inference(instantiation,[status(thm)],[c_792]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_21,negated_conjecture,
% 3.46/1.02      ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
% 3.46/1.02      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.46/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(contradiction,plain,
% 3.46/1.02      ( $false ),
% 3.46/1.02      inference(minisat,
% 3.46/1.02                [status(thm)],
% 3.46/1.02                [c_10849,c_2085,c_1928,c_1564,c_1493,c_819,c_21,c_22,
% 3.46/1.02                 c_23]) ).
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/1.02  
% 3.46/1.02  ------                               Statistics
% 3.46/1.02  
% 3.46/1.02  ------ General
% 3.46/1.02  
% 3.46/1.02  abstr_ref_over_cycles:                  0
% 3.46/1.02  abstr_ref_under_cycles:                 0
% 3.46/1.02  gc_basic_clause_elim:                   0
% 3.46/1.02  forced_gc_time:                         0
% 3.46/1.02  parsing_time:                           0.009
% 3.46/1.02  unif_index_cands_time:                  0.
% 3.46/1.02  unif_index_add_time:                    0.
% 3.46/1.02  orderings_time:                         0.
% 3.46/1.02  out_proof_time:                         0.011
% 3.46/1.02  total_time:                             0.358
% 3.46/1.02  num_of_symbols:                         51
% 3.46/1.02  num_of_terms:                           11502
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing
% 3.46/1.02  
% 3.46/1.02  num_of_splits:                          0
% 3.46/1.02  num_of_split_atoms:                     0
% 3.46/1.02  num_of_reused_defs:                     0
% 3.46/1.02  num_eq_ax_congr_red:                    32
% 3.46/1.02  num_of_sem_filtered_clauses:            1
% 3.46/1.02  num_of_subtypes:                        0
% 3.46/1.02  monotx_restored_types:                  0
% 3.46/1.02  sat_num_of_epr_types:                   0
% 3.46/1.02  sat_num_of_non_cyclic_types:            0
% 3.46/1.02  sat_guarded_non_collapsed_types:        0
% 3.46/1.02  num_pure_diseq_elim:                    0
% 3.46/1.02  simp_replaced_by:                       0
% 3.46/1.02  res_preprocessed:                       119
% 3.46/1.02  prep_upred:                             0
% 3.46/1.02  prep_unflattend:                        18
% 3.46/1.02  smt_new_axioms:                         0
% 3.46/1.02  pred_elim_cands:                        3
% 3.46/1.02  pred_elim:                              1
% 3.46/1.02  pred_elim_cl:                           2
% 3.46/1.02  pred_elim_cycles:                       3
% 3.46/1.02  merged_defs:                            8
% 3.46/1.02  merged_defs_ncl:                        0
% 3.46/1.02  bin_hyper_res:                          9
% 3.46/1.02  prep_cycles:                            4
% 3.46/1.02  pred_elim_time:                         0.004
% 3.46/1.02  splitting_time:                         0.
% 3.46/1.02  sem_filter_time:                        0.
% 3.46/1.02  monotx_time:                            0.
% 3.46/1.02  subtype_inf_time:                       0.
% 3.46/1.02  
% 3.46/1.02  ------ Problem properties
% 3.46/1.02  
% 3.46/1.02  clauses:                                22
% 3.46/1.02  conjectures:                            3
% 3.46/1.02  epr:                                    1
% 3.46/1.02  horn:                                   22
% 3.46/1.02  ground:                                 3
% 3.46/1.02  unary:                                  8
% 3.46/1.02  binary:                                 7
% 3.46/1.02  lits:                                   43
% 3.46/1.02  lits_eq:                                10
% 3.46/1.02  fd_pure:                                0
% 3.46/1.02  fd_pseudo:                              0
% 3.46/1.02  fd_cond:                                0
% 3.46/1.02  fd_pseudo_cond:                         0
% 3.46/1.02  ac_symbols:                             0
% 3.46/1.02  
% 3.46/1.02  ------ Propositional Solver
% 3.46/1.02  
% 3.46/1.02  prop_solver_calls:                      28
% 3.46/1.02  prop_fast_solver_calls:                 815
% 3.46/1.02  smt_solver_calls:                       0
% 3.46/1.02  smt_fast_solver_calls:                  0
% 3.46/1.02  prop_num_of_clauses:                    4734
% 3.46/1.02  prop_preprocess_simplified:             8951
% 3.46/1.02  prop_fo_subsumed:                       9
% 3.46/1.02  prop_solver_time:                       0.
% 3.46/1.02  smt_solver_time:                        0.
% 3.46/1.02  smt_fast_solver_time:                   0.
% 3.46/1.02  prop_fast_solver_time:                  0.
% 3.46/1.02  prop_unsat_core_time:                   0.
% 3.46/1.02  
% 3.46/1.02  ------ QBF
% 3.46/1.02  
% 3.46/1.02  qbf_q_res:                              0
% 3.46/1.02  qbf_num_tautologies:                    0
% 3.46/1.02  qbf_prep_cycles:                        0
% 3.46/1.02  
% 3.46/1.02  ------ BMC1
% 3.46/1.02  
% 3.46/1.02  bmc1_current_bound:                     -1
% 3.46/1.02  bmc1_last_solved_bound:                 -1
% 3.46/1.02  bmc1_unsat_core_size:                   -1
% 3.46/1.02  bmc1_unsat_core_parents_size:           -1
% 3.46/1.02  bmc1_merge_next_fun:                    0
% 3.46/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.46/1.02  
% 3.46/1.02  ------ Instantiation
% 3.46/1.02  
% 3.46/1.02  inst_num_of_clauses:                    1342
% 3.46/1.02  inst_num_in_passive:                    88
% 3.46/1.02  inst_num_in_active:                     584
% 3.46/1.02  inst_num_in_unprocessed:                670
% 3.46/1.02  inst_num_of_loops:                      590
% 3.46/1.02  inst_num_of_learning_restarts:          0
% 3.46/1.02  inst_num_moves_active_passive:          4
% 3.46/1.02  inst_lit_activity:                      0
% 3.46/1.02  inst_lit_activity_moves:                0
% 3.46/1.02  inst_num_tautologies:                   0
% 3.46/1.02  inst_num_prop_implied:                  0
% 3.46/1.02  inst_num_existing_simplified:           0
% 3.46/1.02  inst_num_eq_res_simplified:             0
% 3.46/1.02  inst_num_child_elim:                    0
% 3.46/1.02  inst_num_of_dismatching_blockings:      142
% 3.46/1.02  inst_num_of_non_proper_insts:           939
% 3.46/1.02  inst_num_of_duplicates:                 0
% 3.46/1.02  inst_inst_num_from_inst_to_res:         0
% 3.46/1.02  inst_dismatching_checking_time:         0.
% 3.46/1.02  
% 3.46/1.02  ------ Resolution
% 3.46/1.02  
% 3.46/1.02  res_num_of_clauses:                     0
% 3.46/1.02  res_num_in_passive:                     0
% 3.46/1.02  res_num_in_active:                      0
% 3.46/1.02  res_num_of_loops:                       123
% 3.46/1.02  res_forward_subset_subsumed:            65
% 3.46/1.02  res_backward_subset_subsumed:           0
% 3.46/1.02  res_forward_subsumed:                   0
% 3.46/1.02  res_backward_subsumed:                  0
% 3.46/1.02  res_forward_subsumption_resolution:     0
% 3.46/1.02  res_backward_subsumption_resolution:    0
% 3.46/1.02  res_clause_to_clause_subsumption:       815
% 3.46/1.02  res_orphan_elimination:                 0
% 3.46/1.02  res_tautology_del:                      76
% 3.46/1.02  res_num_eq_res_simplified:              0
% 3.46/1.02  res_num_sel_changes:                    0
% 3.46/1.02  res_moves_from_active_to_pass:          0
% 3.46/1.02  
% 3.46/1.02  ------ Superposition
% 3.46/1.02  
% 3.46/1.02  sup_time_total:                         0.
% 3.46/1.02  sup_time_generating:                    0.
% 3.46/1.02  sup_time_sim_full:                      0.
% 3.46/1.02  sup_time_sim_immed:                     0.
% 3.46/1.02  
% 3.46/1.02  sup_num_of_clauses:                     368
% 3.46/1.02  sup_num_in_active:                      100
% 3.46/1.02  sup_num_in_passive:                     268
% 3.46/1.02  sup_num_of_loops:                       117
% 3.46/1.02  sup_fw_superposition:                   299
% 3.46/1.02  sup_bw_superposition:                   241
% 3.46/1.02  sup_immediate_simplified:               225
% 3.46/1.02  sup_given_eliminated:                   2
% 3.46/1.02  comparisons_done:                       0
% 3.46/1.02  comparisons_avoided:                    0
% 3.46/1.02  
% 3.46/1.02  ------ Simplifications
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  sim_fw_subset_subsumed:                 18
% 3.46/1.02  sim_bw_subset_subsumed:                 4
% 3.46/1.02  sim_fw_subsumed:                        36
% 3.46/1.02  sim_bw_subsumed:                        0
% 3.46/1.02  sim_fw_subsumption_res:                 2
% 3.46/1.02  sim_bw_subsumption_res:                 0
% 3.46/1.02  sim_tautology_del:                      2
% 3.46/1.02  sim_eq_tautology_del:                   6
% 3.46/1.02  sim_eq_res_simp:                        0
% 3.46/1.02  sim_fw_demodulated:                     90
% 3.46/1.02  sim_bw_demodulated:                     27
% 3.46/1.02  sim_light_normalised:                   136
% 3.46/1.02  sim_joinable_taut:                      0
% 3.46/1.02  sim_joinable_simp:                      0
% 3.46/1.02  sim_ac_normalised:                      0
% 3.46/1.02  sim_smt_subsumption:                    0
% 3.46/1.02  
%------------------------------------------------------------------------------
