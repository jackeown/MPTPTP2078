%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:22 EST 2020

% Result     : Theorem 10.94s
% Output     : CNFRefutation 10.94s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 495 expanded)
%              Number of clauses        :  100 ( 209 expanded)
%              Number of leaves         :   22 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          :  357 (1074 expanded)
%              Number of equality atoms :  183 ( 483 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,
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

fof(f38,plain,
    ( ( k2_relset_1(sK0,sK1,sK2) != sK1
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f37])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f68,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f66,f66])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f69,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_257,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_258,plain,
    ( v5_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_356,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_258])).

cnf(c_357,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_795,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_1119,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_795])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_242,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_243,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_800,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_1066,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_800])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1173,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1174,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_1481,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1119,c_1066,c_1174])).

cnf(c_13,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_804,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_806,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2461,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_806])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_43,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18829,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2461,c_43])).

cnf(c_18830,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_18829])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_807,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18841,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18830,c_807])).

cnf(c_21573,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18841,c_43])).

cnf(c_21574,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_21573])).

cnf(c_21580,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1481,c_21574])).

cnf(c_1325,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1066,c_1174])).

cnf(c_803,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_808,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3291,plain,
    ( k9_relat_1(k6_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_808])).

cnf(c_8457,plain,
    ( k9_relat_1(k6_relat_1(X0),k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_1325,c_3291])).

cnf(c_0,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_805,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2580,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_803,c_805])).

cnf(c_15,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1256,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_15,c_9])).

cnf(c_3400,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_2580,c_1256])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_809,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2657,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_803,c_809])).

cnf(c_4849,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3400,c_2657])).

cnf(c_4852,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_4849])).

cnf(c_4982,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_4852,c_4849])).

cnf(c_8489,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) = k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_8457,c_4982])).

cnf(c_1258,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_1256,c_15])).

cnf(c_3408,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_2580,c_1258])).

cnf(c_4264,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3408,c_2657])).

cnf(c_8855,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) ),
    inference(superposition,[status(thm)],[c_8489,c_4264])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10758,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)) = k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_8855,c_10])).

cnf(c_26550,plain,
    ( k2_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) = k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_21580,c_10758])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_801,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( r1_tarski(X0,k2_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_305,plain,
    ( r1_tarski(X0,k2_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_306,plain,
    ( r1_tarski(X0,k2_relset_1(X1,X2,sK2))
    | ~ r1_tarski(k6_relat_1(X0),sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_797,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(X2,k2_relset_1(X0,X1,sK2)) = iProver_top
    | r1_tarski(k6_relat_1(X2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_1072,plain,
    ( r1_tarski(X0,k2_relset_1(sK0,sK1,sK2)) = iProver_top
    | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_797])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_269,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_270,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_967,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_270])).

cnf(c_1073,plain,
    ( r1_tarski(X0,k2_relat_1(sK2)) = iProver_top
    | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1072,c_967])).

cnf(c_1433,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_1073])).

cnf(c_21583,plain,
    ( k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k6_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1433,c_21574])).

cnf(c_8487,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) = k7_relat_1(k6_relat_1(X0),k2_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_8457,c_4264])).

cnf(c_9146,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(sK2))) = k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_8487,c_10])).

cnf(c_22142,plain,
    ( k2_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) = k1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_21583,c_9146])).

cnf(c_22168,plain,
    ( k2_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) = sK1 ),
    inference(demodulation,[status(thm)],[c_22142,c_10])).

cnf(c_26756,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK2))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_26550,c_22168])).

cnf(c_495,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4113,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK2))) != X0
    | sK1 != X0
    | sK1 = k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_4114,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK2))) != sK1
    | sK1 = k1_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4113])).

cnf(c_1114,plain,
    ( k2_relset_1(sK0,sK1,sK2) != X0
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_2565,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_2326,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK2))) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1314,plain,
    ( X0 != X1
    | k2_relset_1(sK0,sK1,sK2) != X1
    | k2_relset_1(sK0,sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_1457,plain,
    ( X0 != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = X0
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_2325,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k1_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k1_relat_1(k6_relat_1(k2_relat_1(sK2))) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_20,plain,
    ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_290,plain,
    ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_291,plain,
    ( r1_tarski(X0,k1_relset_1(X1,X2,sK2))
    | ~ r1_tarski(k6_relat_1(X0),sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1053,plain,
    ( r1_tarski(X0,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_tarski(k6_relat_1(X0),sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_1055,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_947,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_494,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_946,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_523,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26756,c_4114,c_2565,c_2326,c_2325,c_1055,c_947,c_946,c_523,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:07:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 10.94/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/2.00  
% 10.94/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.94/2.00  
% 10.94/2.00  ------  iProver source info
% 10.94/2.00  
% 10.94/2.00  git: date: 2020-06-30 10:37:57 +0100
% 10.94/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.94/2.00  git: non_committed_changes: false
% 10.94/2.00  git: last_make_outside_of_git: false
% 10.94/2.00  
% 10.94/2.00  ------ 
% 10.94/2.00  
% 10.94/2.00  ------ Input Options
% 10.94/2.00  
% 10.94/2.00  --out_options                           all
% 10.94/2.00  --tptp_safe_out                         true
% 10.94/2.00  --problem_path                          ""
% 10.94/2.00  --include_path                          ""
% 10.94/2.00  --clausifier                            res/vclausify_rel
% 10.94/2.00  --clausifier_options                    --mode clausify
% 10.94/2.00  --stdin                                 false
% 10.94/2.00  --stats_out                             all
% 10.94/2.00  
% 10.94/2.00  ------ General Options
% 10.94/2.00  
% 10.94/2.00  --fof                                   false
% 10.94/2.00  --time_out_real                         305.
% 10.94/2.00  --time_out_virtual                      -1.
% 10.94/2.00  --symbol_type_check                     false
% 10.94/2.00  --clausify_out                          false
% 10.94/2.00  --sig_cnt_out                           false
% 10.94/2.00  --trig_cnt_out                          false
% 10.94/2.00  --trig_cnt_out_tolerance                1.
% 10.94/2.00  --trig_cnt_out_sk_spl                   false
% 10.94/2.00  --abstr_cl_out                          false
% 10.94/2.00  
% 10.94/2.00  ------ Global Options
% 10.94/2.00  
% 10.94/2.00  --schedule                              default
% 10.94/2.00  --add_important_lit                     false
% 10.94/2.00  --prop_solver_per_cl                    1000
% 10.94/2.00  --min_unsat_core                        false
% 10.94/2.00  --soft_assumptions                      false
% 10.94/2.00  --soft_lemma_size                       3
% 10.94/2.00  --prop_impl_unit_size                   0
% 10.94/2.00  --prop_impl_unit                        []
% 10.94/2.00  --share_sel_clauses                     true
% 10.94/2.00  --reset_solvers                         false
% 10.94/2.00  --bc_imp_inh                            [conj_cone]
% 10.94/2.00  --conj_cone_tolerance                   3.
% 10.94/2.00  --extra_neg_conj                        none
% 10.94/2.00  --large_theory_mode                     true
% 10.94/2.00  --prolific_symb_bound                   200
% 10.94/2.00  --lt_threshold                          2000
% 10.94/2.00  --clause_weak_htbl                      true
% 10.94/2.00  --gc_record_bc_elim                     false
% 10.94/2.00  
% 10.94/2.00  ------ Preprocessing Options
% 10.94/2.00  
% 10.94/2.00  --preprocessing_flag                    true
% 10.94/2.00  --time_out_prep_mult                    0.1
% 10.94/2.00  --splitting_mode                        input
% 10.94/2.00  --splitting_grd                         true
% 10.94/2.00  --splitting_cvd                         false
% 10.94/2.00  --splitting_cvd_svl                     false
% 10.94/2.00  --splitting_nvd                         32
% 10.94/2.00  --sub_typing                            true
% 10.94/2.00  --prep_gs_sim                           true
% 10.94/2.00  --prep_unflatten                        true
% 10.94/2.00  --prep_res_sim                          true
% 10.94/2.00  --prep_upred                            true
% 10.94/2.00  --prep_sem_filter                       exhaustive
% 10.94/2.00  --prep_sem_filter_out                   false
% 10.94/2.00  --pred_elim                             true
% 10.94/2.00  --res_sim_input                         true
% 10.94/2.00  --eq_ax_congr_red                       true
% 10.94/2.00  --pure_diseq_elim                       true
% 10.94/2.00  --brand_transform                       false
% 10.94/2.00  --non_eq_to_eq                          false
% 10.94/2.00  --prep_def_merge                        true
% 10.94/2.00  --prep_def_merge_prop_impl              false
% 10.94/2.00  --prep_def_merge_mbd                    true
% 10.94/2.00  --prep_def_merge_tr_red                 false
% 10.94/2.00  --prep_def_merge_tr_cl                  false
% 10.94/2.00  --smt_preprocessing                     true
% 10.94/2.00  --smt_ac_axioms                         fast
% 10.94/2.00  --preprocessed_out                      false
% 10.94/2.00  --preprocessed_stats                    false
% 10.94/2.00  
% 10.94/2.00  ------ Abstraction refinement Options
% 10.94/2.00  
% 10.94/2.00  --abstr_ref                             []
% 10.94/2.00  --abstr_ref_prep                        false
% 10.94/2.00  --abstr_ref_until_sat                   false
% 10.94/2.00  --abstr_ref_sig_restrict                funpre
% 10.94/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 10.94/2.00  --abstr_ref_under                       []
% 10.94/2.00  
% 10.94/2.00  ------ SAT Options
% 10.94/2.00  
% 10.94/2.00  --sat_mode                              false
% 10.94/2.00  --sat_fm_restart_options                ""
% 10.94/2.00  --sat_gr_def                            false
% 10.94/2.00  --sat_epr_types                         true
% 10.94/2.00  --sat_non_cyclic_types                  false
% 10.94/2.00  --sat_finite_models                     false
% 10.94/2.00  --sat_fm_lemmas                         false
% 10.94/2.00  --sat_fm_prep                           false
% 10.94/2.00  --sat_fm_uc_incr                        true
% 10.94/2.00  --sat_out_model                         small
% 10.94/2.00  --sat_out_clauses                       false
% 10.94/2.00  
% 10.94/2.00  ------ QBF Options
% 10.94/2.00  
% 10.94/2.00  --qbf_mode                              false
% 10.94/2.00  --qbf_elim_univ                         false
% 10.94/2.00  --qbf_dom_inst                          none
% 10.94/2.00  --qbf_dom_pre_inst                      false
% 10.94/2.00  --qbf_sk_in                             false
% 10.94/2.00  --qbf_pred_elim                         true
% 10.94/2.00  --qbf_split                             512
% 10.94/2.00  
% 10.94/2.00  ------ BMC1 Options
% 10.94/2.00  
% 10.94/2.00  --bmc1_incremental                      false
% 10.94/2.00  --bmc1_axioms                           reachable_all
% 10.94/2.00  --bmc1_min_bound                        0
% 10.94/2.00  --bmc1_max_bound                        -1
% 10.94/2.00  --bmc1_max_bound_default                -1
% 10.94/2.00  --bmc1_symbol_reachability              true
% 10.94/2.00  --bmc1_property_lemmas                  false
% 10.94/2.00  --bmc1_k_induction                      false
% 10.94/2.00  --bmc1_non_equiv_states                 false
% 10.94/2.00  --bmc1_deadlock                         false
% 10.94/2.00  --bmc1_ucm                              false
% 10.94/2.00  --bmc1_add_unsat_core                   none
% 10.94/2.00  --bmc1_unsat_core_children              false
% 10.94/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 10.94/2.00  --bmc1_out_stat                         full
% 10.94/2.00  --bmc1_ground_init                      false
% 10.94/2.00  --bmc1_pre_inst_next_state              false
% 10.94/2.00  --bmc1_pre_inst_state                   false
% 10.94/2.00  --bmc1_pre_inst_reach_state             false
% 10.94/2.00  --bmc1_out_unsat_core                   false
% 10.94/2.00  --bmc1_aig_witness_out                  false
% 10.94/2.00  --bmc1_verbose                          false
% 10.94/2.00  --bmc1_dump_clauses_tptp                false
% 10.94/2.00  --bmc1_dump_unsat_core_tptp             false
% 10.94/2.00  --bmc1_dump_file                        -
% 10.94/2.00  --bmc1_ucm_expand_uc_limit              128
% 10.94/2.00  --bmc1_ucm_n_expand_iterations          6
% 10.94/2.00  --bmc1_ucm_extend_mode                  1
% 10.94/2.00  --bmc1_ucm_init_mode                    2
% 10.94/2.00  --bmc1_ucm_cone_mode                    none
% 10.94/2.00  --bmc1_ucm_reduced_relation_type        0
% 10.94/2.00  --bmc1_ucm_relax_model                  4
% 10.94/2.00  --bmc1_ucm_full_tr_after_sat            true
% 10.94/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 10.94/2.00  --bmc1_ucm_layered_model                none
% 10.94/2.00  --bmc1_ucm_max_lemma_size               10
% 10.94/2.00  
% 10.94/2.00  ------ AIG Options
% 10.94/2.00  
% 10.94/2.00  --aig_mode                              false
% 10.94/2.00  
% 10.94/2.00  ------ Instantiation Options
% 10.94/2.00  
% 10.94/2.00  --instantiation_flag                    true
% 10.94/2.00  --inst_sos_flag                         false
% 10.94/2.00  --inst_sos_phase                        true
% 10.94/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.94/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.94/2.00  --inst_lit_sel_side                     num_symb
% 10.94/2.00  --inst_solver_per_active                1400
% 10.94/2.00  --inst_solver_calls_frac                1.
% 10.94/2.00  --inst_passive_queue_type               priority_queues
% 10.94/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.94/2.00  --inst_passive_queues_freq              [25;2]
% 10.94/2.00  --inst_dismatching                      true
% 10.94/2.00  --inst_eager_unprocessed_to_passive     true
% 10.94/2.00  --inst_prop_sim_given                   true
% 10.94/2.00  --inst_prop_sim_new                     false
% 10.94/2.00  --inst_subs_new                         false
% 10.94/2.00  --inst_eq_res_simp                      false
% 10.94/2.00  --inst_subs_given                       false
% 10.94/2.00  --inst_orphan_elimination               true
% 10.94/2.00  --inst_learning_loop_flag               true
% 10.94/2.00  --inst_learning_start                   3000
% 10.94/2.00  --inst_learning_factor                  2
% 10.94/2.00  --inst_start_prop_sim_after_learn       3
% 10.94/2.00  --inst_sel_renew                        solver
% 10.94/2.00  --inst_lit_activity_flag                true
% 10.94/2.00  --inst_restr_to_given                   false
% 10.94/2.00  --inst_activity_threshold               500
% 10.94/2.00  --inst_out_proof                        true
% 10.94/2.00  
% 10.94/2.00  ------ Resolution Options
% 10.94/2.00  
% 10.94/2.00  --resolution_flag                       true
% 10.94/2.00  --res_lit_sel                           adaptive
% 10.94/2.00  --res_lit_sel_side                      none
% 10.94/2.00  --res_ordering                          kbo
% 10.94/2.00  --res_to_prop_solver                    active
% 10.94/2.00  --res_prop_simpl_new                    false
% 10.94/2.00  --res_prop_simpl_given                  true
% 10.94/2.00  --res_passive_queue_type                priority_queues
% 10.94/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.94/2.00  --res_passive_queues_freq               [15;5]
% 10.94/2.00  --res_forward_subs                      full
% 10.94/2.00  --res_backward_subs                     full
% 10.94/2.00  --res_forward_subs_resolution           true
% 10.94/2.00  --res_backward_subs_resolution          true
% 10.94/2.00  --res_orphan_elimination                true
% 10.94/2.00  --res_time_limit                        2.
% 10.94/2.00  --res_out_proof                         true
% 10.94/2.00  
% 10.94/2.00  ------ Superposition Options
% 10.94/2.00  
% 10.94/2.00  --superposition_flag                    true
% 10.94/2.00  --sup_passive_queue_type                priority_queues
% 10.94/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.94/2.00  --sup_passive_queues_freq               [8;1;4]
% 10.94/2.00  --demod_completeness_check              fast
% 10.94/2.00  --demod_use_ground                      true
% 10.94/2.00  --sup_to_prop_solver                    passive
% 10.94/2.00  --sup_prop_simpl_new                    true
% 10.94/2.00  --sup_prop_simpl_given                  true
% 10.94/2.00  --sup_fun_splitting                     false
% 10.94/2.00  --sup_smt_interval                      50000
% 10.94/2.00  
% 10.94/2.00  ------ Superposition Simplification Setup
% 10.94/2.00  
% 10.94/2.00  --sup_indices_passive                   []
% 10.94/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.94/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.94/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.94/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 10.94/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.94/2.00  --sup_full_bw                           [BwDemod]
% 10.94/2.00  --sup_immed_triv                        [TrivRules]
% 10.94/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.94/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.94/2.00  --sup_immed_bw_main                     []
% 10.94/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.94/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 10.94/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.94/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.94/2.00  
% 10.94/2.00  ------ Combination Options
% 10.94/2.00  
% 10.94/2.00  --comb_res_mult                         3
% 10.94/2.00  --comb_sup_mult                         2
% 10.94/2.00  --comb_inst_mult                        10
% 10.94/2.00  
% 10.94/2.00  ------ Debug Options
% 10.94/2.00  
% 10.94/2.00  --dbg_backtrace                         false
% 10.94/2.00  --dbg_dump_prop_clauses                 false
% 10.94/2.00  --dbg_dump_prop_clauses_file            -
% 10.94/2.00  --dbg_out_stat                          false
% 10.94/2.00  ------ Parsing...
% 10.94/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.94/2.00  
% 10.94/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 10.94/2.00  
% 10.94/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.94/2.00  
% 10.94/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.94/2.00  ------ Proving...
% 10.94/2.00  ------ Problem Properties 
% 10.94/2.00  
% 10.94/2.00  
% 10.94/2.00  clauses                                 21
% 10.94/2.00  conjectures                             2
% 10.94/2.00  EPR                                     1
% 10.94/2.00  Horn                                    21
% 10.94/2.00  unary                                   9
% 10.94/2.00  binary                                  5
% 10.94/2.00  lits                                    41
% 10.94/2.00  lits eq                                 16
% 10.94/2.00  fd_pure                                 0
% 10.94/2.00  fd_pseudo                               0
% 10.94/2.00  fd_cond                                 0
% 10.94/2.00  fd_pseudo_cond                          0
% 10.94/2.00  AC symbols                              0
% 10.94/2.00  
% 10.94/2.00  ------ Schedule dynamic 5 is on 
% 10.94/2.00  
% 10.94/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 10.94/2.00  
% 10.94/2.00  
% 10.94/2.00  ------ 
% 10.94/2.00  Current options:
% 10.94/2.00  ------ 
% 10.94/2.00  
% 10.94/2.00  ------ Input Options
% 10.94/2.00  
% 10.94/2.00  --out_options                           all
% 10.94/2.00  --tptp_safe_out                         true
% 10.94/2.00  --problem_path                          ""
% 10.94/2.00  --include_path                          ""
% 10.94/2.00  --clausifier                            res/vclausify_rel
% 10.94/2.00  --clausifier_options                    --mode clausify
% 10.94/2.00  --stdin                                 false
% 10.94/2.00  --stats_out                             all
% 10.94/2.00  
% 10.94/2.00  ------ General Options
% 10.94/2.00  
% 10.94/2.00  --fof                                   false
% 10.94/2.00  --time_out_real                         305.
% 10.94/2.00  --time_out_virtual                      -1.
% 10.94/2.00  --symbol_type_check                     false
% 10.94/2.00  --clausify_out                          false
% 10.94/2.00  --sig_cnt_out                           false
% 10.94/2.00  --trig_cnt_out                          false
% 10.94/2.00  --trig_cnt_out_tolerance                1.
% 10.94/2.00  --trig_cnt_out_sk_spl                   false
% 10.94/2.00  --abstr_cl_out                          false
% 10.94/2.00  
% 10.94/2.00  ------ Global Options
% 10.94/2.00  
% 10.94/2.00  --schedule                              default
% 10.94/2.00  --add_important_lit                     false
% 10.94/2.00  --prop_solver_per_cl                    1000
% 10.94/2.00  --min_unsat_core                        false
% 10.94/2.00  --soft_assumptions                      false
% 10.94/2.00  --soft_lemma_size                       3
% 10.94/2.00  --prop_impl_unit_size                   0
% 10.94/2.00  --prop_impl_unit                        []
% 10.94/2.00  --share_sel_clauses                     true
% 10.94/2.00  --reset_solvers                         false
% 10.94/2.00  --bc_imp_inh                            [conj_cone]
% 10.94/2.00  --conj_cone_tolerance                   3.
% 10.94/2.00  --extra_neg_conj                        none
% 10.94/2.00  --large_theory_mode                     true
% 10.94/2.00  --prolific_symb_bound                   200
% 10.94/2.00  --lt_threshold                          2000
% 10.94/2.00  --clause_weak_htbl                      true
% 10.94/2.00  --gc_record_bc_elim                     false
% 10.94/2.00  
% 10.94/2.00  ------ Preprocessing Options
% 10.94/2.00  
% 10.94/2.00  --preprocessing_flag                    true
% 10.94/2.00  --time_out_prep_mult                    0.1
% 10.94/2.00  --splitting_mode                        input
% 10.94/2.00  --splitting_grd                         true
% 10.94/2.00  --splitting_cvd                         false
% 10.94/2.00  --splitting_cvd_svl                     false
% 10.94/2.00  --splitting_nvd                         32
% 10.94/2.00  --sub_typing                            true
% 10.94/2.00  --prep_gs_sim                           true
% 10.94/2.00  --prep_unflatten                        true
% 10.94/2.00  --prep_res_sim                          true
% 10.94/2.00  --prep_upred                            true
% 10.94/2.00  --prep_sem_filter                       exhaustive
% 10.94/2.00  --prep_sem_filter_out                   false
% 10.94/2.00  --pred_elim                             true
% 10.94/2.00  --res_sim_input                         true
% 10.94/2.00  --eq_ax_congr_red                       true
% 10.94/2.00  --pure_diseq_elim                       true
% 10.94/2.00  --brand_transform                       false
% 10.94/2.00  --non_eq_to_eq                          false
% 10.94/2.00  --prep_def_merge                        true
% 10.94/2.00  --prep_def_merge_prop_impl              false
% 10.94/2.00  --prep_def_merge_mbd                    true
% 10.94/2.00  --prep_def_merge_tr_red                 false
% 10.94/2.00  --prep_def_merge_tr_cl                  false
% 10.94/2.00  --smt_preprocessing                     true
% 10.94/2.00  --smt_ac_axioms                         fast
% 10.94/2.00  --preprocessed_out                      false
% 10.94/2.00  --preprocessed_stats                    false
% 10.94/2.00  
% 10.94/2.00  ------ Abstraction refinement Options
% 10.94/2.00  
% 10.94/2.00  --abstr_ref                             []
% 10.94/2.00  --abstr_ref_prep                        false
% 10.94/2.00  --abstr_ref_until_sat                   false
% 10.94/2.00  --abstr_ref_sig_restrict                funpre
% 10.94/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 10.94/2.00  --abstr_ref_under                       []
% 10.94/2.00  
% 10.94/2.00  ------ SAT Options
% 10.94/2.00  
% 10.94/2.00  --sat_mode                              false
% 10.94/2.00  --sat_fm_restart_options                ""
% 10.94/2.00  --sat_gr_def                            false
% 10.94/2.00  --sat_epr_types                         true
% 10.94/2.00  --sat_non_cyclic_types                  false
% 10.94/2.00  --sat_finite_models                     false
% 10.94/2.00  --sat_fm_lemmas                         false
% 10.94/2.00  --sat_fm_prep                           false
% 10.94/2.00  --sat_fm_uc_incr                        true
% 10.94/2.00  --sat_out_model                         small
% 10.94/2.00  --sat_out_clauses                       false
% 10.94/2.00  
% 10.94/2.00  ------ QBF Options
% 10.94/2.00  
% 10.94/2.00  --qbf_mode                              false
% 10.94/2.00  --qbf_elim_univ                         false
% 10.94/2.00  --qbf_dom_inst                          none
% 10.94/2.00  --qbf_dom_pre_inst                      false
% 10.94/2.00  --qbf_sk_in                             false
% 10.94/2.00  --qbf_pred_elim                         true
% 10.94/2.00  --qbf_split                             512
% 10.94/2.00  
% 10.94/2.00  ------ BMC1 Options
% 10.94/2.00  
% 10.94/2.00  --bmc1_incremental                      false
% 10.94/2.00  --bmc1_axioms                           reachable_all
% 10.94/2.00  --bmc1_min_bound                        0
% 10.94/2.00  --bmc1_max_bound                        -1
% 10.94/2.00  --bmc1_max_bound_default                -1
% 10.94/2.00  --bmc1_symbol_reachability              true
% 10.94/2.00  --bmc1_property_lemmas                  false
% 10.94/2.00  --bmc1_k_induction                      false
% 10.94/2.00  --bmc1_non_equiv_states                 false
% 10.94/2.00  --bmc1_deadlock                         false
% 10.94/2.00  --bmc1_ucm                              false
% 10.94/2.00  --bmc1_add_unsat_core                   none
% 10.94/2.00  --bmc1_unsat_core_children              false
% 10.94/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 10.94/2.00  --bmc1_out_stat                         full
% 10.94/2.00  --bmc1_ground_init                      false
% 10.94/2.00  --bmc1_pre_inst_next_state              false
% 10.94/2.00  --bmc1_pre_inst_state                   false
% 10.94/2.00  --bmc1_pre_inst_reach_state             false
% 10.94/2.00  --bmc1_out_unsat_core                   false
% 10.94/2.00  --bmc1_aig_witness_out                  false
% 10.94/2.00  --bmc1_verbose                          false
% 10.94/2.00  --bmc1_dump_clauses_tptp                false
% 10.94/2.00  --bmc1_dump_unsat_core_tptp             false
% 10.94/2.00  --bmc1_dump_file                        -
% 10.94/2.00  --bmc1_ucm_expand_uc_limit              128
% 10.94/2.00  --bmc1_ucm_n_expand_iterations          6
% 10.94/2.00  --bmc1_ucm_extend_mode                  1
% 10.94/2.00  --bmc1_ucm_init_mode                    2
% 10.94/2.00  --bmc1_ucm_cone_mode                    none
% 10.94/2.00  --bmc1_ucm_reduced_relation_type        0
% 10.94/2.00  --bmc1_ucm_relax_model                  4
% 10.94/2.00  --bmc1_ucm_full_tr_after_sat            true
% 10.94/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 10.94/2.00  --bmc1_ucm_layered_model                none
% 10.94/2.00  --bmc1_ucm_max_lemma_size               10
% 10.94/2.00  
% 10.94/2.00  ------ AIG Options
% 10.94/2.00  
% 10.94/2.00  --aig_mode                              false
% 10.94/2.00  
% 10.94/2.00  ------ Instantiation Options
% 10.94/2.00  
% 10.94/2.00  --instantiation_flag                    true
% 10.94/2.00  --inst_sos_flag                         false
% 10.94/2.00  --inst_sos_phase                        true
% 10.94/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.94/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.94/2.00  --inst_lit_sel_side                     none
% 10.94/2.00  --inst_solver_per_active                1400
% 10.94/2.00  --inst_solver_calls_frac                1.
% 10.94/2.00  --inst_passive_queue_type               priority_queues
% 10.94/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.94/2.00  --inst_passive_queues_freq              [25;2]
% 10.94/2.00  --inst_dismatching                      true
% 10.94/2.00  --inst_eager_unprocessed_to_passive     true
% 10.94/2.00  --inst_prop_sim_given                   true
% 10.94/2.00  --inst_prop_sim_new                     false
% 10.94/2.00  --inst_subs_new                         false
% 10.94/2.00  --inst_eq_res_simp                      false
% 10.94/2.00  --inst_subs_given                       false
% 10.94/2.00  --inst_orphan_elimination               true
% 10.94/2.00  --inst_learning_loop_flag               true
% 10.94/2.00  --inst_learning_start                   3000
% 10.94/2.00  --inst_learning_factor                  2
% 10.94/2.00  --inst_start_prop_sim_after_learn       3
% 10.94/2.00  --inst_sel_renew                        solver
% 10.94/2.00  --inst_lit_activity_flag                true
% 10.94/2.00  --inst_restr_to_given                   false
% 10.94/2.00  --inst_activity_threshold               500
% 10.94/2.00  --inst_out_proof                        true
% 10.94/2.00  
% 10.94/2.00  ------ Resolution Options
% 10.94/2.00  
% 10.94/2.00  --resolution_flag                       false
% 10.94/2.00  --res_lit_sel                           adaptive
% 10.94/2.00  --res_lit_sel_side                      none
% 10.94/2.00  --res_ordering                          kbo
% 10.94/2.00  --res_to_prop_solver                    active
% 10.94/2.00  --res_prop_simpl_new                    false
% 10.94/2.00  --res_prop_simpl_given                  true
% 10.94/2.00  --res_passive_queue_type                priority_queues
% 10.94/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.94/2.00  --res_passive_queues_freq               [15;5]
% 10.94/2.00  --res_forward_subs                      full
% 10.94/2.00  --res_backward_subs                     full
% 10.94/2.00  --res_forward_subs_resolution           true
% 10.94/2.00  --res_backward_subs_resolution          true
% 10.94/2.00  --res_orphan_elimination                true
% 10.94/2.00  --res_time_limit                        2.
% 10.94/2.00  --res_out_proof                         true
% 10.94/2.00  
% 10.94/2.00  ------ Superposition Options
% 10.94/2.00  
% 10.94/2.00  --superposition_flag                    true
% 10.94/2.00  --sup_passive_queue_type                priority_queues
% 10.94/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.94/2.00  --sup_passive_queues_freq               [8;1;4]
% 10.94/2.00  --demod_completeness_check              fast
% 10.94/2.00  --demod_use_ground                      true
% 10.94/2.00  --sup_to_prop_solver                    passive
% 10.94/2.00  --sup_prop_simpl_new                    true
% 10.94/2.00  --sup_prop_simpl_given                  true
% 10.94/2.00  --sup_fun_splitting                     false
% 10.94/2.00  --sup_smt_interval                      50000
% 10.94/2.00  
% 10.94/2.00  ------ Superposition Simplification Setup
% 10.94/2.00  
% 10.94/2.00  --sup_indices_passive                   []
% 10.94/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.94/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.94/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.94/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 10.94/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.94/2.00  --sup_full_bw                           [BwDemod]
% 10.94/2.00  --sup_immed_triv                        [TrivRules]
% 10.94/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.94/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.94/2.00  --sup_immed_bw_main                     []
% 10.94/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.94/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 10.94/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.94/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.94/2.00  
% 10.94/2.00  ------ Combination Options
% 10.94/2.00  
% 10.94/2.00  --comb_res_mult                         3
% 10.94/2.00  --comb_sup_mult                         2
% 10.94/2.00  --comb_inst_mult                        10
% 10.94/2.00  
% 10.94/2.00  ------ Debug Options
% 10.94/2.00  
% 10.94/2.00  --dbg_backtrace                         false
% 10.94/2.00  --dbg_dump_prop_clauses                 false
% 10.94/2.00  --dbg_dump_prop_clauses_file            -
% 10.94/2.00  --dbg_out_stat                          false
% 10.94/2.00  
% 10.94/2.00  
% 10.94/2.00  
% 10.94/2.00  
% 10.94/2.00  ------ Proving...
% 10.94/2.00  
% 10.94/2.00  
% 10.94/2.00  % SZS status Theorem for theBenchmark.p
% 10.94/2.00  
% 10.94/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 10.94/2.00  
% 10.94/2.00  fof(f6,axiom,(
% 10.94/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f22,plain,(
% 10.94/2.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 10.94/2.00    inference(ennf_transformation,[],[f6])).
% 10.94/2.00  
% 10.94/2.00  fof(f36,plain,(
% 10.94/2.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 10.94/2.00    inference(nnf_transformation,[],[f22])).
% 10.94/2.00  
% 10.94/2.00  fof(f44,plain,(
% 10.94/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f36])).
% 10.94/2.00  
% 10.94/2.00  fof(f16,axiom,(
% 10.94/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f30,plain,(
% 10.94/2.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.94/2.00    inference(ennf_transformation,[],[f16])).
% 10.94/2.00  
% 10.94/2.00  fof(f59,plain,(
% 10.94/2.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.94/2.00    inference(cnf_transformation,[],[f30])).
% 10.94/2.00  
% 10.94/2.00  fof(f19,conjecture,(
% 10.94/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f20,negated_conjecture,(
% 10.94/2.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 10.94/2.00    inference(negated_conjecture,[],[f19])).
% 10.94/2.00  
% 10.94/2.00  fof(f34,plain,(
% 10.94/2.00    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.94/2.00    inference(ennf_transformation,[],[f20])).
% 10.94/2.00  
% 10.94/2.00  fof(f35,plain,(
% 10.94/2.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.94/2.00    inference(flattening,[],[f34])).
% 10.94/2.00  
% 10.94/2.00  fof(f37,plain,(
% 10.94/2.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 10.94/2.00    introduced(choice_axiom,[])).
% 10.94/2.00  
% 10.94/2.00  fof(f38,plain,(
% 10.94/2.00    (k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 10.94/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f37])).
% 10.94/2.00  
% 10.94/2.00  fof(f63,plain,(
% 10.94/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 10.94/2.00    inference(cnf_transformation,[],[f38])).
% 10.94/2.00  
% 10.94/2.00  fof(f5,axiom,(
% 10.94/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f21,plain,(
% 10.94/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 10.94/2.00    inference(ennf_transformation,[],[f5])).
% 10.94/2.00  
% 10.94/2.00  fof(f43,plain,(
% 10.94/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f21])).
% 10.94/2.00  
% 10.94/2.00  fof(f7,axiom,(
% 10.94/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f46,plain,(
% 10.94/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 10.94/2.00    inference(cnf_transformation,[],[f7])).
% 10.94/2.00  
% 10.94/2.00  fof(f14,axiom,(
% 10.94/2.00    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f55,plain,(
% 10.94/2.00    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f14])).
% 10.94/2.00  
% 10.94/2.00  fof(f11,axiom,(
% 10.94/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f27,plain,(
% 10.94/2.00    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 10.94/2.00    inference(ennf_transformation,[],[f11])).
% 10.94/2.00  
% 10.94/2.00  fof(f28,plain,(
% 10.94/2.00    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 10.94/2.00    inference(flattening,[],[f27])).
% 10.94/2.00  
% 10.94/2.00  fof(f50,plain,(
% 10.94/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f28])).
% 10.94/2.00  
% 10.94/2.00  fof(f54,plain,(
% 10.94/2.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 10.94/2.00    inference(cnf_transformation,[],[f14])).
% 10.94/2.00  
% 10.94/2.00  fof(f10,axiom,(
% 10.94/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f25,plain,(
% 10.94/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 10.94/2.00    inference(ennf_transformation,[],[f10])).
% 10.94/2.00  
% 10.94/2.00  fof(f26,plain,(
% 10.94/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 10.94/2.00    inference(flattening,[],[f25])).
% 10.94/2.00  
% 10.94/2.00  fof(f49,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f26])).
% 10.94/2.00  
% 10.94/2.00  fof(f9,axiom,(
% 10.94/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f24,plain,(
% 10.94/2.00    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.94/2.00    inference(ennf_transformation,[],[f9])).
% 10.94/2.00  
% 10.94/2.00  fof(f48,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f24])).
% 10.94/2.00  
% 10.94/2.00  fof(f1,axiom,(
% 10.94/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f39,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f1])).
% 10.94/2.00  
% 10.94/2.00  fof(f2,axiom,(
% 10.94/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f40,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f2])).
% 10.94/2.00  
% 10.94/2.00  fof(f3,axiom,(
% 10.94/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f41,plain,(
% 10.94/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f3])).
% 10.94/2.00  
% 10.94/2.00  fof(f66,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 10.94/2.00    inference(definition_unfolding,[],[f40,f41])).
% 10.94/2.00  
% 10.94/2.00  fof(f68,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 10.94/2.00    inference(definition_unfolding,[],[f39,f66,f66])).
% 10.94/2.00  
% 10.94/2.00  fof(f13,axiom,(
% 10.94/2.00    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f29,plain,(
% 10.94/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 10.94/2.00    inference(ennf_transformation,[],[f13])).
% 10.94/2.00  
% 10.94/2.00  fof(f53,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f29])).
% 10.94/2.00  
% 10.94/2.00  fof(f15,axiom,(
% 10.94/2.00    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f57,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 10.94/2.00    inference(cnf_transformation,[],[f15])).
% 10.94/2.00  
% 10.94/2.00  fof(f4,axiom,(
% 10.94/2.00    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f42,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f4])).
% 10.94/2.00  
% 10.94/2.00  fof(f67,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 10.94/2.00    inference(definition_unfolding,[],[f42,f66])).
% 10.94/2.00  
% 10.94/2.00  fof(f69,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 10.94/2.00    inference(definition_unfolding,[],[f57,f67])).
% 10.94/2.00  
% 10.94/2.00  fof(f12,axiom,(
% 10.94/2.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f52,plain,(
% 10.94/2.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 10.94/2.00    inference(cnf_transformation,[],[f12])).
% 10.94/2.00  
% 10.94/2.00  fof(f8,axiom,(
% 10.94/2.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f23,plain,(
% 10.94/2.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 10.94/2.00    inference(ennf_transformation,[],[f8])).
% 10.94/2.00  
% 10.94/2.00  fof(f47,plain,(
% 10.94/2.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.94/2.00    inference(cnf_transformation,[],[f23])).
% 10.94/2.00  
% 10.94/2.00  fof(f51,plain,(
% 10.94/2.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 10.94/2.00    inference(cnf_transformation,[],[f12])).
% 10.94/2.00  
% 10.94/2.00  fof(f64,plain,(
% 10.94/2.00    r1_tarski(k6_relat_1(sK1),sK2)),
% 10.94/2.00    inference(cnf_transformation,[],[f38])).
% 10.94/2.00  
% 10.94/2.00  fof(f18,axiom,(
% 10.94/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f32,plain,(
% 10.94/2.00    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.94/2.00    inference(ennf_transformation,[],[f18])).
% 10.94/2.00  
% 10.94/2.00  fof(f33,plain,(
% 10.94/2.00    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.94/2.00    inference(flattening,[],[f32])).
% 10.94/2.00  
% 10.94/2.00  fof(f62,plain,(
% 10.94/2.00    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.94/2.00    inference(cnf_transformation,[],[f33])).
% 10.94/2.00  
% 10.94/2.00  fof(f17,axiom,(
% 10.94/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 10.94/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.94/2.00  
% 10.94/2.00  fof(f31,plain,(
% 10.94/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.94/2.00    inference(ennf_transformation,[],[f17])).
% 10.94/2.00  
% 10.94/2.00  fof(f60,plain,(
% 10.94/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.94/2.00    inference(cnf_transformation,[],[f31])).
% 10.94/2.00  
% 10.94/2.00  fof(f61,plain,(
% 10.94/2.00    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.94/2.00    inference(cnf_transformation,[],[f33])).
% 10.94/2.00  
% 10.94/2.00  fof(f65,plain,(
% 10.94/2.00    k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 10.94/2.00    inference(cnf_transformation,[],[f38])).
% 10.94/2.00  
% 10.94/2.00  cnf(c_3,plain,
% 10.94/2.00      ( r1_tarski(k2_relat_1(X0),X1)
% 10.94/2.00      | ~ v5_relat_1(X0,X1)
% 10.94/2.00      | ~ v1_relat_1(X0) ),
% 10.94/2.00      inference(cnf_transformation,[],[f44]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_16,plain,
% 10.94/2.00      ( v5_relat_1(X0,X1)
% 10.94/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 10.94/2.00      inference(cnf_transformation,[],[f59]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_23,negated_conjecture,
% 10.94/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 10.94/2.00      inference(cnf_transformation,[],[f63]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_257,plain,
% 10.94/2.00      ( v5_relat_1(X0,X1)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 10.94/2.00      | sK2 != X0 ),
% 10.94/2.00      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_258,plain,
% 10.94/2.00      ( v5_relat_1(sK2,X0)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(unflattening,[status(thm)],[c_257]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_356,plain,
% 10.94/2.00      ( r1_tarski(k2_relat_1(X0),X1)
% 10.94/2.00      | ~ v1_relat_1(X0)
% 10.94/2.00      | X2 != X1
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 10.94/2.00      | sK2 != X0 ),
% 10.94/2.00      inference(resolution_lifted,[status(thm)],[c_3,c_258]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_357,plain,
% 10.94/2.00      ( r1_tarski(k2_relat_1(sK2),X0)
% 10.94/2.00      | ~ v1_relat_1(sK2)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(unflattening,[status(thm)],[c_356]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_795,plain,
% 10.94/2.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 10.94/2.00      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 10.94/2.00      | v1_relat_1(sK2) != iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1119,plain,
% 10.94/2.00      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 10.94/2.00      | v1_relat_1(sK2) != iProver_top ),
% 10.94/2.00      inference(equality_resolution,[status(thm)],[c_795]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1,plain,
% 10.94/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 10.94/2.00      | ~ v1_relat_1(X1)
% 10.94/2.00      | v1_relat_1(X0) ),
% 10.94/2.00      inference(cnf_transformation,[],[f43]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_242,plain,
% 10.94/2.00      ( ~ v1_relat_1(X0)
% 10.94/2.00      | v1_relat_1(X1)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 10.94/2.00      | sK2 != X1 ),
% 10.94/2.00      inference(resolution_lifted,[status(thm)],[c_1,c_23]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_243,plain,
% 10.94/2.00      ( ~ v1_relat_1(X0)
% 10.94/2.00      | v1_relat_1(sK2)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
% 10.94/2.00      inference(unflattening,[status(thm)],[c_242]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_800,plain,
% 10.94/2.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 10.94/2.00      | v1_relat_1(X0) != iProver_top
% 10.94/2.00      | v1_relat_1(sK2) = iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1066,plain,
% 10.94/2.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 10.94/2.00      | v1_relat_1(sK2) = iProver_top ),
% 10.94/2.00      inference(equality_resolution,[status(thm)],[c_800]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_4,plain,
% 10.94/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 10.94/2.00      inference(cnf_transformation,[],[f46]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1173,plain,
% 10.94/2.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1174,plain,
% 10.94/2.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1481,plain,
% 10.94/2.00      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 10.94/2.00      inference(global_propositional_subsumption,
% 10.94/2.00                [status(thm)],
% 10.94/2.00                [c_1119,c_1066,c_1174]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_13,plain,
% 10.94/2.00      ( v4_relat_1(k6_relat_1(X0),X0) ),
% 10.94/2.00      inference(cnf_transformation,[],[f55]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_804,plain,
% 10.94/2.00      ( v4_relat_1(k6_relat_1(X0),X0) = iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_8,plain,
% 10.94/2.00      ( ~ v4_relat_1(X0,X1)
% 10.94/2.00      | v4_relat_1(X0,X2)
% 10.94/2.00      | ~ r1_tarski(X1,X2)
% 10.94/2.00      | ~ v1_relat_1(X0) ),
% 10.94/2.00      inference(cnf_transformation,[],[f50]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_806,plain,
% 10.94/2.00      ( v4_relat_1(X0,X1) != iProver_top
% 10.94/2.00      | v4_relat_1(X0,X2) = iProver_top
% 10.94/2.00      | r1_tarski(X1,X2) != iProver_top
% 10.94/2.00      | v1_relat_1(X0) != iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_2461,plain,
% 10.94/2.00      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 10.94/2.00      | r1_tarski(X0,X1) != iProver_top
% 10.94/2.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_804,c_806]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_14,plain,
% 10.94/2.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 10.94/2.00      inference(cnf_transformation,[],[f54]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_43,plain,
% 10.94/2.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_18829,plain,
% 10.94/2.00      ( r1_tarski(X0,X1) != iProver_top
% 10.94/2.00      | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
% 10.94/2.00      inference(global_propositional_subsumption,
% 10.94/2.00                [status(thm)],
% 10.94/2.00                [c_2461,c_43]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_18830,plain,
% 10.94/2.00      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 10.94/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 10.94/2.00      inference(renaming,[status(thm)],[c_18829]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_7,plain,
% 10.94/2.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 10.94/2.00      inference(cnf_transformation,[],[f49]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_807,plain,
% 10.94/2.00      ( k7_relat_1(X0,X1) = X0
% 10.94/2.00      | v4_relat_1(X0,X1) != iProver_top
% 10.94/2.00      | v1_relat_1(X0) != iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_18841,plain,
% 10.94/2.00      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 10.94/2.00      | r1_tarski(X0,X1) != iProver_top
% 10.94/2.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_18830,c_807]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_21573,plain,
% 10.94/2.00      ( r1_tarski(X0,X1) != iProver_top
% 10.94/2.00      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 10.94/2.00      inference(global_propositional_subsumption,
% 10.94/2.00                [status(thm)],
% 10.94/2.00                [c_18841,c_43]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_21574,plain,
% 10.94/2.00      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 10.94/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 10.94/2.00      inference(renaming,[status(thm)],[c_21573]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_21580,plain,
% 10.94/2.00      ( k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k6_relat_1(k2_relat_1(sK2)) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_1481,c_21574]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1325,plain,
% 10.94/2.00      ( v1_relat_1(sK2) = iProver_top ),
% 10.94/2.00      inference(global_propositional_subsumption,
% 10.94/2.00                [status(thm)],
% 10.94/2.00                [c_1066,c_1174]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_803,plain,
% 10.94/2.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_6,plain,
% 10.94/2.00      ( ~ v1_relat_1(X0)
% 10.94/2.00      | ~ v1_relat_1(X1)
% 10.94/2.00      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 10.94/2.00      inference(cnf_transformation,[],[f48]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_808,plain,
% 10.94/2.00      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 10.94/2.00      | v1_relat_1(X1) != iProver_top
% 10.94/2.00      | v1_relat_1(X0) != iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_3291,plain,
% 10.94/2.00      ( k9_relat_1(k6_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 10.94/2.00      | v1_relat_1(X1) != iProver_top ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_803,c_808]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_8457,plain,
% 10.94/2.00      ( k9_relat_1(k6_relat_1(X0),k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_1325,c_3291]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_0,plain,
% 10.94/2.00      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 10.94/2.00      inference(cnf_transformation,[],[f68]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_11,plain,
% 10.94/2.00      ( ~ v1_relat_1(X0)
% 10.94/2.00      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 10.94/2.00      inference(cnf_transformation,[],[f53]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_805,plain,
% 10.94/2.00      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 10.94/2.00      | v1_relat_1(X1) != iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_2580,plain,
% 10.94/2.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_803,c_805]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_15,plain,
% 10.94/2.00      ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 10.94/2.00      inference(cnf_transformation,[],[f69]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_9,plain,
% 10.94/2.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 10.94/2.00      inference(cnf_transformation,[],[f52]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1256,plain,
% 10.94/2.00      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_15,c_9]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_3400,plain,
% 10.94/2.00      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 10.94/2.00      inference(demodulation,[status(thm)],[c_2580,c_1256]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_5,plain,
% 10.94/2.00      ( ~ v1_relat_1(X0)
% 10.94/2.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 10.94/2.00      inference(cnf_transformation,[],[f47]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_809,plain,
% 10.94/2.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 10.94/2.00      | v1_relat_1(X0) != iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_2657,plain,
% 10.94/2.00      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_803,c_809]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_4849,plain,
% 10.94/2.00      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 10.94/2.00      inference(light_normalisation,[status(thm)],[c_3400,c_2657]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_4852,plain,
% 10.94/2.00      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_0,c_4849]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_4982,plain,
% 10.94/2.00      ( k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_4852,c_4849]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_8489,plain,
% 10.94/2.00      ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) = k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_8457,c_4982]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1258,plain,
% 10.94/2.00      ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 10.94/2.00      inference(demodulation,[status(thm)],[c_1256,c_15]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_3408,plain,
% 10.94/2.00      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 10.94/2.00      inference(demodulation,[status(thm)],[c_2580,c_1258]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_4264,plain,
% 10.94/2.00      ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 10.94/2.00      inference(light_normalisation,[status(thm)],[c_3408,c_2657]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_8855,plain,
% 10.94/2.00      ( k6_relat_1(k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_8489,c_4264]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_10,plain,
% 10.94/2.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 10.94/2.00      inference(cnf_transformation,[],[f51]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_10758,plain,
% 10.94/2.00      ( k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)) = k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_8855,c_10]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_26550,plain,
% 10.94/2.00      ( k2_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) = k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_21580,c_10758]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_22,negated_conjecture,
% 10.94/2.00      ( r1_tarski(k6_relat_1(sK1),sK2) ),
% 10.94/2.00      inference(cnf_transformation,[],[f64]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_801,plain,
% 10.94/2.00      ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_19,plain,
% 10.94/2.00      ( r1_tarski(X0,k2_relset_1(X1,X2,X3))
% 10.94/2.00      | ~ r1_tarski(k6_relat_1(X0),X3)
% 10.94/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 10.94/2.00      inference(cnf_transformation,[],[f62]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_305,plain,
% 10.94/2.00      ( r1_tarski(X0,k2_relset_1(X1,X2,X3))
% 10.94/2.00      | ~ r1_tarski(k6_relat_1(X0),X3)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 10.94/2.00      | sK2 != X3 ),
% 10.94/2.00      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_306,plain,
% 10.94/2.00      ( r1_tarski(X0,k2_relset_1(X1,X2,sK2))
% 10.94/2.00      | ~ r1_tarski(k6_relat_1(X0),sK2)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(unflattening,[status(thm)],[c_305]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_797,plain,
% 10.94/2.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 10.94/2.00      | r1_tarski(X2,k2_relset_1(X0,X1,sK2)) = iProver_top
% 10.94/2.00      | r1_tarski(k6_relat_1(X2),sK2) != iProver_top ),
% 10.94/2.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1072,plain,
% 10.94/2.00      ( r1_tarski(X0,k2_relset_1(sK0,sK1,sK2)) = iProver_top
% 10.94/2.00      | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
% 10.94/2.00      inference(equality_resolution,[status(thm)],[c_797]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_18,plain,
% 10.94/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 10.94/2.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 10.94/2.00      inference(cnf_transformation,[],[f60]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_269,plain,
% 10.94/2.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 10.94/2.00      | sK2 != X2 ),
% 10.94/2.00      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_270,plain,
% 10.94/2.00      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(unflattening,[status(thm)],[c_269]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_967,plain,
% 10.94/2.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 10.94/2.00      inference(equality_resolution,[status(thm)],[c_270]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1073,plain,
% 10.94/2.00      ( r1_tarski(X0,k2_relat_1(sK2)) = iProver_top
% 10.94/2.00      | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
% 10.94/2.00      inference(light_normalisation,[status(thm)],[c_1072,c_967]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1433,plain,
% 10.94/2.00      ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_801,c_1073]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_21583,plain,
% 10.94/2.00      ( k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) = k6_relat_1(sK1) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_1433,c_21574]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_8487,plain,
% 10.94/2.00      ( k6_relat_1(k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) = k7_relat_1(k6_relat_1(X0),k2_relat_1(sK2)) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_8457,c_4264]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_9146,plain,
% 10.94/2.00      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(sK2))) = k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_8487,c_10]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_22142,plain,
% 10.94/2.00      ( k2_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) = k1_relat_1(k6_relat_1(sK1)) ),
% 10.94/2.00      inference(superposition,[status(thm)],[c_21583,c_9146]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_22168,plain,
% 10.94/2.00      ( k2_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) = sK1 ),
% 10.94/2.00      inference(demodulation,[status(thm)],[c_22142,c_10]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_26756,plain,
% 10.94/2.00      ( k1_relat_1(k6_relat_1(k2_relat_1(sK2))) = sK1 ),
% 10.94/2.00      inference(light_normalisation,[status(thm)],[c_26550,c_22168]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_495,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_4113,plain,
% 10.94/2.00      ( k1_relat_1(k6_relat_1(k2_relat_1(sK2))) != X0
% 10.94/2.00      | sK1 != X0
% 10.94/2.00      | sK1 = k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_495]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_4114,plain,
% 10.94/2.00      ( k1_relat_1(k6_relat_1(k2_relat_1(sK2))) != sK1
% 10.94/2.00      | sK1 = k1_relat_1(k6_relat_1(k2_relat_1(sK2)))
% 10.94/2.00      | sK1 != sK1 ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_4113]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1114,plain,
% 10.94/2.00      ( k2_relset_1(sK0,sK1,sK2) != X0
% 10.94/2.00      | k2_relset_1(sK0,sK1,sK2) = sK1
% 10.94/2.00      | sK1 != X0 ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_495]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_2565,plain,
% 10.94/2.00      ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k6_relat_1(k2_relat_1(sK2)))
% 10.94/2.00      | k2_relset_1(sK0,sK1,sK2) = sK1
% 10.94/2.00      | sK1 != k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_1114]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_2326,plain,
% 10.94/2.00      ( k1_relat_1(k6_relat_1(k2_relat_1(sK2))) = k2_relat_1(sK2) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1314,plain,
% 10.94/2.00      ( X0 != X1
% 10.94/2.00      | k2_relset_1(sK0,sK1,sK2) != X1
% 10.94/2.00      | k2_relset_1(sK0,sK1,sK2) = X0 ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_495]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1457,plain,
% 10.94/2.00      ( X0 != k2_relat_1(sK2)
% 10.94/2.00      | k2_relset_1(sK0,sK1,sK2) = X0
% 10.94/2.00      | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_1314]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_2325,plain,
% 10.94/2.00      ( k2_relset_1(sK0,sK1,sK2) = k1_relat_1(k6_relat_1(k2_relat_1(sK2)))
% 10.94/2.00      | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 10.94/2.00      | k1_relat_1(k6_relat_1(k2_relat_1(sK2))) != k2_relat_1(sK2) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_1457]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_20,plain,
% 10.94/2.00      ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
% 10.94/2.00      | ~ r1_tarski(k6_relat_1(X0),X3)
% 10.94/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 10.94/2.00      inference(cnf_transformation,[],[f61]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_290,plain,
% 10.94/2.00      ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
% 10.94/2.00      | ~ r1_tarski(k6_relat_1(X0),X3)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 10.94/2.00      | sK2 != X3 ),
% 10.94/2.00      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_291,plain,
% 10.94/2.00      ( r1_tarski(X0,k1_relset_1(X1,X2,sK2))
% 10.94/2.00      | ~ r1_tarski(k6_relat_1(X0),sK2)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(unflattening,[status(thm)],[c_290]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1053,plain,
% 10.94/2.00      ( r1_tarski(X0,k1_relset_1(sK0,sK1,sK2))
% 10.94/2.00      | ~ r1_tarski(k6_relat_1(X0),sK2)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_291]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_1055,plain,
% 10.94/2.00      ( ~ r1_tarski(k6_relat_1(sK1),sK2)
% 10.94/2.00      | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_1053]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_947,plain,
% 10.94/2.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
% 10.94/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_270]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_494,plain,( X0 = X0 ),theory(equality) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_946,plain,
% 10.94/2.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_494]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_523,plain,
% 10.94/2.00      ( sK1 = sK1 ),
% 10.94/2.00      inference(instantiation,[status(thm)],[c_494]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(c_21,negated_conjecture,
% 10.94/2.00      ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
% 10.94/2.00      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 10.94/2.00      inference(cnf_transformation,[],[f65]) ).
% 10.94/2.00  
% 10.94/2.00  cnf(contradiction,plain,
% 10.94/2.00      ( $false ),
% 10.94/2.00      inference(minisat,
% 10.94/2.00                [status(thm)],
% 10.94/2.00                [c_26756,c_4114,c_2565,c_2326,c_2325,c_1055,c_947,c_946,
% 10.94/2.00                 c_523,c_21,c_22]) ).
% 10.94/2.00  
% 10.94/2.00  
% 10.94/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 10.94/2.00  
% 10.94/2.00  ------                               Statistics
% 10.94/2.00  
% 10.94/2.00  ------ General
% 10.94/2.00  
% 10.94/2.00  abstr_ref_over_cycles:                  0
% 10.94/2.00  abstr_ref_under_cycles:                 0
% 10.94/2.00  gc_basic_clause_elim:                   0
% 10.94/2.00  forced_gc_time:                         0
% 10.94/2.00  parsing_time:                           0.01
% 10.94/2.00  unif_index_cands_time:                  0.
% 10.94/2.00  unif_index_add_time:                    0.
% 10.94/2.00  orderings_time:                         0.
% 10.94/2.00  out_proof_time:                         0.013
% 10.94/2.00  total_time:                             1.065
% 10.94/2.00  num_of_symbols:                         51
% 10.94/2.00  num_of_terms:                           45560
% 10.94/2.00  
% 10.94/2.00  ------ Preprocessing
% 10.94/2.00  
% 10.94/2.00  num_of_splits:                          0
% 10.94/2.00  num_of_split_atoms:                     0
% 10.94/2.00  num_of_reused_defs:                     0
% 10.94/2.00  num_eq_ax_congr_red:                    25
% 10.94/2.00  num_of_sem_filtered_clauses:            1
% 10.94/2.00  num_of_subtypes:                        0
% 10.94/2.00  monotx_restored_types:                  0
% 10.94/2.00  sat_num_of_epr_types:                   0
% 10.94/2.00  sat_num_of_non_cyclic_types:            0
% 10.94/2.00  sat_guarded_non_collapsed_types:        0
% 10.94/2.00  num_pure_diseq_elim:                    0
% 10.94/2.00  simp_replaced_by:                       0
% 10.94/2.00  res_preprocessed:                       118
% 10.94/2.00  prep_upred:                             0
% 10.94/2.00  prep_unflattend:                        10
% 10.94/2.00  smt_new_axioms:                         0
% 10.94/2.00  pred_elim_cands:                        3
% 10.94/2.00  pred_elim:                              2
% 10.94/2.00  pred_elim_cl:                           3
% 10.94/2.00  pred_elim_cycles:                       4
% 10.94/2.00  merged_defs:                            0
% 10.94/2.00  merged_defs_ncl:                        0
% 10.94/2.00  bin_hyper_res:                          0
% 10.94/2.00  prep_cycles:                            4
% 10.94/2.00  pred_elim_time:                         0.004
% 10.94/2.00  splitting_time:                         0.
% 10.94/2.00  sem_filter_time:                        0.
% 10.94/2.00  monotx_time:                            0.
% 10.94/2.00  subtype_inf_time:                       0.
% 10.94/2.00  
% 10.94/2.00  ------ Problem properties
% 10.94/2.00  
% 10.94/2.00  clauses:                                21
% 10.94/2.00  conjectures:                            2
% 10.94/2.00  epr:                                    1
% 10.94/2.00  horn:                                   21
% 10.94/2.00  ground:                                 2
% 10.94/2.00  unary:                                  9
% 10.94/2.00  binary:                                 5
% 10.94/2.00  lits:                                   41
% 10.94/2.00  lits_eq:                                16
% 10.94/2.00  fd_pure:                                0
% 10.94/2.00  fd_pseudo:                              0
% 10.94/2.00  fd_cond:                                0
% 10.94/2.00  fd_pseudo_cond:                         0
% 10.94/2.00  ac_symbols:                             0
% 10.94/2.00  
% 10.94/2.00  ------ Propositional Solver
% 10.94/2.00  
% 10.94/2.00  prop_solver_calls:                      31
% 10.94/2.00  prop_fast_solver_calls:                 901
% 10.94/2.00  smt_solver_calls:                       0
% 10.94/2.00  smt_fast_solver_calls:                  0
% 10.94/2.00  prop_num_of_clauses:                    10975
% 10.94/2.00  prop_preprocess_simplified:             15504
% 10.94/2.00  prop_fo_subsumed:                       11
% 10.94/2.00  prop_solver_time:                       0.
% 10.94/2.00  smt_solver_time:                        0.
% 10.94/2.00  smt_fast_solver_time:                   0.
% 10.94/2.00  prop_fast_solver_time:                  0.
% 10.94/2.00  prop_unsat_core_time:                   0.001
% 10.94/2.00  
% 10.94/2.00  ------ QBF
% 10.94/2.00  
% 10.94/2.00  qbf_q_res:                              0
% 10.94/2.00  qbf_num_tautologies:                    0
% 10.94/2.00  qbf_prep_cycles:                        0
% 10.94/2.00  
% 10.94/2.00  ------ BMC1
% 10.94/2.00  
% 10.94/2.00  bmc1_current_bound:                     -1
% 10.94/2.00  bmc1_last_solved_bound:                 -1
% 10.94/2.00  bmc1_unsat_core_size:                   -1
% 10.94/2.00  bmc1_unsat_core_parents_size:           -1
% 10.94/2.00  bmc1_merge_next_fun:                    0
% 10.94/2.00  bmc1_unsat_core_clauses_time:           0.
% 10.94/2.00  
% 10.94/2.00  ------ Instantiation
% 10.94/2.00  
% 10.94/2.00  inst_num_of_clauses:                    2750
% 10.94/2.00  inst_num_in_passive:                    1414
% 10.94/2.00  inst_num_in_active:                     1113
% 10.94/2.00  inst_num_in_unprocessed:                225
% 10.94/2.00  inst_num_of_loops:                      1120
% 10.94/2.00  inst_num_of_learning_restarts:          0
% 10.94/2.00  inst_num_moves_active_passive:          4
% 10.94/2.00  inst_lit_activity:                      0
% 10.94/2.00  inst_lit_activity_moves:                0
% 10.94/2.00  inst_num_tautologies:                   0
% 10.94/2.00  inst_num_prop_implied:                  0
% 10.94/2.00  inst_num_existing_simplified:           0
% 10.94/2.00  inst_num_eq_res_simplified:             0
% 10.94/2.00  inst_num_child_elim:                    0
% 10.94/2.00  inst_num_of_dismatching_blockings:      843
% 10.94/2.00  inst_num_of_non_proper_insts:           2289
% 10.94/2.00  inst_num_of_duplicates:                 0
% 10.94/2.00  inst_inst_num_from_inst_to_res:         0
% 10.94/2.00  inst_dismatching_checking_time:         0.
% 10.94/2.00  
% 10.94/2.00  ------ Resolution
% 10.94/2.00  
% 10.94/2.00  res_num_of_clauses:                     0
% 10.94/2.00  res_num_in_passive:                     0
% 10.94/2.00  res_num_in_active:                      0
% 10.94/2.00  res_num_of_loops:                       122
% 10.94/2.00  res_forward_subset_subsumed:            353
% 10.94/2.00  res_backward_subset_subsumed:           8
% 10.94/2.00  res_forward_subsumed:                   0
% 10.94/2.00  res_backward_subsumed:                  0
% 10.94/2.00  res_forward_subsumption_resolution:     0
% 10.94/2.00  res_backward_subsumption_resolution:    0
% 10.94/2.00  res_clause_to_clause_subsumption:       4807
% 10.94/2.00  res_orphan_elimination:                 0
% 10.94/2.00  res_tautology_del:                      382
% 10.94/2.00  res_num_eq_res_simplified:              0
% 10.94/2.00  res_num_sel_changes:                    0
% 10.94/2.00  res_moves_from_active_to_pass:          0
% 10.94/2.00  
% 10.94/2.00  ------ Superposition
% 10.94/2.00  
% 10.94/2.00  sup_time_total:                         0.
% 10.94/2.00  sup_time_generating:                    0.
% 10.94/2.00  sup_time_sim_full:                      0.
% 10.94/2.00  sup_time_sim_immed:                     0.
% 10.94/2.00  
% 10.94/2.00  sup_num_of_clauses:                     1846
% 10.94/2.00  sup_num_in_active:                      192
% 10.94/2.00  sup_num_in_passive:                     1654
% 10.94/2.00  sup_num_of_loops:                       222
% 10.94/2.00  sup_fw_superposition:                   1467
% 10.94/2.00  sup_bw_superposition:                   1515
% 10.94/2.00  sup_immediate_simplified:               2245
% 10.94/2.00  sup_given_eliminated:                   4
% 10.94/2.00  comparisons_done:                       0
% 10.94/2.00  comparisons_avoided:                    0
% 10.94/2.00  
% 10.94/2.00  ------ Simplifications
% 10.94/2.00  
% 10.94/2.00  
% 10.94/2.00  sim_fw_subset_subsumed:                 12
% 10.94/2.00  sim_bw_subset_subsumed:                 8
% 10.94/2.00  sim_fw_subsumed:                        197
% 10.94/2.00  sim_bw_subsumed:                        106
% 10.94/2.00  sim_fw_subsumption_res:                 0
% 10.94/2.00  sim_bw_subsumption_res:                 0
% 10.94/2.00  sim_tautology_del:                      0
% 10.94/2.00  sim_eq_tautology_del:                   155
% 10.94/2.00  sim_eq_res_simp:                        0
% 10.94/2.00  sim_fw_demodulated:                     1049
% 10.94/2.00  sim_bw_demodulated:                     74
% 10.94/2.00  sim_light_normalised:                   1107
% 10.94/2.00  sim_joinable_taut:                      0
% 10.94/2.00  sim_joinable_simp:                      0
% 10.94/2.00  sim_ac_normalised:                      0
% 10.94/2.00  sim_smt_subsumption:                    0
% 10.94/2.00  
%------------------------------------------------------------------------------
