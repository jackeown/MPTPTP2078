%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:48 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 988 expanded)
%              Number of clauses        :   57 ( 187 expanded)
%              Number of leaves         :   18 ( 257 expanded)
%              Depth                    :   23
%              Number of atoms          :  318 (2342 expanded)
%              Number of equality atoms :  207 (1249 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f33])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f63])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f60,f64])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f39,f38,f63,f63,f63,f64,f64,f64,f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f64,f64])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f62,f64,f64])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2162,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3071,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2159,c_2162])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2163,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3199,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3071,c_2163])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3388,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3199,c_26])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2168,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3393,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3388,c_2168])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2170,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3716,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3393,c_2170])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_302,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_303,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_2158,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_304,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2324,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2324])).

cnf(c_2332,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2158,c_26,c_304,c_2325])).

cnf(c_2333,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_2332])).

cnf(c_3736,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3716,c_2333])).

cnf(c_4235,plain,
    ( k2_enumset1(k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0))) = k2_relat_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3736,c_2333])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2167,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2161,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3180,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2159,c_2161])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2160,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3265,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3180,c_2160])).

cnf(c_4238,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3736,c_3265])).

cnf(c_4295,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2167,c_4238])).

cnf(c_4363,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4235,c_26,c_2325,c_4295])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2165,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4384,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4363,c_2165])).

cnf(c_2444,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1638,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2483,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1639,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2774,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_2959,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2774])).

cnf(c_4301,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2959])).

cnf(c_4471,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4384,c_23,c_26,c_2324,c_2325,c_2444,c_2483,c_4295,c_4301])).

cnf(c_4477,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4471,c_3265])).

cnf(c_13,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4489,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4477,c_13])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2179,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4627,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4489,c_2179])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.97/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.00  
% 2.97/1.00  ------  iProver source info
% 2.97/1.00  
% 2.97/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.00  git: non_committed_changes: false
% 2.97/1.00  git: last_make_outside_of_git: false
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options
% 2.97/1.00  
% 2.97/1.00  --out_options                           all
% 2.97/1.00  --tptp_safe_out                         true
% 2.97/1.00  --problem_path                          ""
% 2.97/1.00  --include_path                          ""
% 2.97/1.00  --clausifier                            res/vclausify_rel
% 2.97/1.00  --clausifier_options                    --mode clausify
% 2.97/1.00  --stdin                                 false
% 2.97/1.00  --stats_out                             all
% 2.97/1.00  
% 2.97/1.00  ------ General Options
% 2.97/1.00  
% 2.97/1.00  --fof                                   false
% 2.97/1.00  --time_out_real                         305.
% 2.97/1.00  --time_out_virtual                      -1.
% 2.97/1.00  --symbol_type_check                     false
% 2.97/1.00  --clausify_out                          false
% 2.97/1.00  --sig_cnt_out                           false
% 2.97/1.00  --trig_cnt_out                          false
% 2.97/1.00  --trig_cnt_out_tolerance                1.
% 2.97/1.00  --trig_cnt_out_sk_spl                   false
% 2.97/1.00  --abstr_cl_out                          false
% 2.97/1.00  
% 2.97/1.00  ------ Global Options
% 2.97/1.00  
% 2.97/1.00  --schedule                              default
% 2.97/1.00  --add_important_lit                     false
% 2.97/1.00  --prop_solver_per_cl                    1000
% 2.97/1.00  --min_unsat_core                        false
% 2.97/1.00  --soft_assumptions                      false
% 2.97/1.00  --soft_lemma_size                       3
% 2.97/1.00  --prop_impl_unit_size                   0
% 2.97/1.00  --prop_impl_unit                        []
% 2.97/1.00  --share_sel_clauses                     true
% 2.97/1.00  --reset_solvers                         false
% 2.97/1.00  --bc_imp_inh                            [conj_cone]
% 2.97/1.00  --conj_cone_tolerance                   3.
% 2.97/1.00  --extra_neg_conj                        none
% 2.97/1.00  --large_theory_mode                     true
% 2.97/1.00  --prolific_symb_bound                   200
% 2.97/1.00  --lt_threshold                          2000
% 2.97/1.00  --clause_weak_htbl                      true
% 2.97/1.00  --gc_record_bc_elim                     false
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing Options
% 2.97/1.00  
% 2.97/1.00  --preprocessing_flag                    true
% 2.97/1.00  --time_out_prep_mult                    0.1
% 2.97/1.00  --splitting_mode                        input
% 2.97/1.00  --splitting_grd                         true
% 2.97/1.00  --splitting_cvd                         false
% 2.97/1.00  --splitting_cvd_svl                     false
% 2.97/1.00  --splitting_nvd                         32
% 2.97/1.00  --sub_typing                            true
% 2.97/1.00  --prep_gs_sim                           true
% 2.97/1.00  --prep_unflatten                        true
% 2.97/1.00  --prep_res_sim                          true
% 2.97/1.00  --prep_upred                            true
% 2.97/1.00  --prep_sem_filter                       exhaustive
% 2.97/1.00  --prep_sem_filter_out                   false
% 2.97/1.00  --pred_elim                             true
% 2.97/1.00  --res_sim_input                         true
% 2.97/1.00  --eq_ax_congr_red                       true
% 2.97/1.00  --pure_diseq_elim                       true
% 2.97/1.00  --brand_transform                       false
% 2.97/1.00  --non_eq_to_eq                          false
% 2.97/1.00  --prep_def_merge                        true
% 2.97/1.00  --prep_def_merge_prop_impl              false
% 2.97/1.00  --prep_def_merge_mbd                    true
% 2.97/1.00  --prep_def_merge_tr_red                 false
% 2.97/1.00  --prep_def_merge_tr_cl                  false
% 2.97/1.00  --smt_preprocessing                     true
% 2.97/1.00  --smt_ac_axioms                         fast
% 2.97/1.00  --preprocessed_out                      false
% 2.97/1.00  --preprocessed_stats                    false
% 2.97/1.00  
% 2.97/1.00  ------ Abstraction refinement Options
% 2.97/1.00  
% 2.97/1.00  --abstr_ref                             []
% 2.97/1.00  --abstr_ref_prep                        false
% 2.97/1.00  --abstr_ref_until_sat                   false
% 2.97/1.00  --abstr_ref_sig_restrict                funpre
% 2.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.00  --abstr_ref_under                       []
% 2.97/1.00  
% 2.97/1.00  ------ SAT Options
% 2.97/1.00  
% 2.97/1.00  --sat_mode                              false
% 2.97/1.00  --sat_fm_restart_options                ""
% 2.97/1.00  --sat_gr_def                            false
% 2.97/1.00  --sat_epr_types                         true
% 2.97/1.00  --sat_non_cyclic_types                  false
% 2.97/1.00  --sat_finite_models                     false
% 2.97/1.00  --sat_fm_lemmas                         false
% 2.97/1.00  --sat_fm_prep                           false
% 2.97/1.00  --sat_fm_uc_incr                        true
% 2.97/1.00  --sat_out_model                         small
% 2.97/1.00  --sat_out_clauses                       false
% 2.97/1.00  
% 2.97/1.00  ------ QBF Options
% 2.97/1.00  
% 2.97/1.00  --qbf_mode                              false
% 2.97/1.00  --qbf_elim_univ                         false
% 2.97/1.00  --qbf_dom_inst                          none
% 2.97/1.00  --qbf_dom_pre_inst                      false
% 2.97/1.00  --qbf_sk_in                             false
% 2.97/1.00  --qbf_pred_elim                         true
% 2.97/1.00  --qbf_split                             512
% 2.97/1.00  
% 2.97/1.00  ------ BMC1 Options
% 2.97/1.00  
% 2.97/1.00  --bmc1_incremental                      false
% 2.97/1.00  --bmc1_axioms                           reachable_all
% 2.97/1.00  --bmc1_min_bound                        0
% 2.97/1.00  --bmc1_max_bound                        -1
% 2.97/1.00  --bmc1_max_bound_default                -1
% 2.97/1.00  --bmc1_symbol_reachability              true
% 2.97/1.00  --bmc1_property_lemmas                  false
% 2.97/1.00  --bmc1_k_induction                      false
% 2.97/1.00  --bmc1_non_equiv_states                 false
% 2.97/1.00  --bmc1_deadlock                         false
% 2.97/1.00  --bmc1_ucm                              false
% 2.97/1.00  --bmc1_add_unsat_core                   none
% 2.97/1.00  --bmc1_unsat_core_children              false
% 2.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.00  --bmc1_out_stat                         full
% 2.97/1.00  --bmc1_ground_init                      false
% 2.97/1.00  --bmc1_pre_inst_next_state              false
% 2.97/1.00  --bmc1_pre_inst_state                   false
% 2.97/1.00  --bmc1_pre_inst_reach_state             false
% 2.97/1.00  --bmc1_out_unsat_core                   false
% 2.97/1.00  --bmc1_aig_witness_out                  false
% 2.97/1.00  --bmc1_verbose                          false
% 2.97/1.00  --bmc1_dump_clauses_tptp                false
% 2.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.00  --bmc1_dump_file                        -
% 2.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.00  --bmc1_ucm_extend_mode                  1
% 2.97/1.00  --bmc1_ucm_init_mode                    2
% 2.97/1.00  --bmc1_ucm_cone_mode                    none
% 2.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.00  --bmc1_ucm_relax_model                  4
% 2.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.00  --bmc1_ucm_layered_model                none
% 2.97/1.00  --bmc1_ucm_max_lemma_size               10
% 2.97/1.00  
% 2.97/1.00  ------ AIG Options
% 2.97/1.00  
% 2.97/1.00  --aig_mode                              false
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation Options
% 2.97/1.00  
% 2.97/1.00  --instantiation_flag                    true
% 2.97/1.00  --inst_sos_flag                         false
% 2.97/1.00  --inst_sos_phase                        true
% 2.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel_side                     num_symb
% 2.97/1.00  --inst_solver_per_active                1400
% 2.97/1.00  --inst_solver_calls_frac                1.
% 2.97/1.00  --inst_passive_queue_type               priority_queues
% 2.97/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.00  --inst_passive_queues_freq              [25;2]
% 2.97/1.00  --inst_dismatching                      true
% 2.97/1.00  --inst_eager_unprocessed_to_passive     true
% 2.97/1.00  --inst_prop_sim_given                   true
% 2.97/1.00  --inst_prop_sim_new                     false
% 2.97/1.00  --inst_subs_new                         false
% 2.97/1.00  --inst_eq_res_simp                      false
% 2.97/1.00  --inst_subs_given                       false
% 2.97/1.00  --inst_orphan_elimination               true
% 2.97/1.00  --inst_learning_loop_flag               true
% 2.97/1.00  --inst_learning_start                   3000
% 2.97/1.00  --inst_learning_factor                  2
% 2.97/1.00  --inst_start_prop_sim_after_learn       3
% 2.97/1.00  --inst_sel_renew                        solver
% 2.97/1.00  --inst_lit_activity_flag                true
% 2.97/1.00  --inst_restr_to_given                   false
% 2.97/1.00  --inst_activity_threshold               500
% 2.97/1.00  --inst_out_proof                        true
% 2.97/1.00  
% 2.97/1.00  ------ Resolution Options
% 2.97/1.00  
% 2.97/1.00  --resolution_flag                       true
% 2.97/1.00  --res_lit_sel                           adaptive
% 2.97/1.00  --res_lit_sel_side                      none
% 2.97/1.00  --res_ordering                          kbo
% 2.97/1.00  --res_to_prop_solver                    active
% 2.97/1.00  --res_prop_simpl_new                    false
% 2.97/1.00  --res_prop_simpl_given                  true
% 2.97/1.00  --res_passive_queue_type                priority_queues
% 2.97/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.00  --res_passive_queues_freq               [15;5]
% 2.97/1.00  --res_forward_subs                      full
% 2.97/1.00  --res_backward_subs                     full
% 2.97/1.00  --res_forward_subs_resolution           true
% 2.97/1.00  --res_backward_subs_resolution          true
% 2.97/1.00  --res_orphan_elimination                true
% 2.97/1.00  --res_time_limit                        2.
% 2.97/1.00  --res_out_proof                         true
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Options
% 2.97/1.00  
% 2.97/1.00  --superposition_flag                    true
% 2.97/1.00  --sup_passive_queue_type                priority_queues
% 2.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.00  --demod_completeness_check              fast
% 2.97/1.00  --demod_use_ground                      true
% 2.97/1.00  --sup_to_prop_solver                    passive
% 2.97/1.00  --sup_prop_simpl_new                    true
% 2.97/1.00  --sup_prop_simpl_given                  true
% 2.97/1.00  --sup_fun_splitting                     false
% 2.97/1.00  --sup_smt_interval                      50000
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Simplification Setup
% 2.97/1.00  
% 2.97/1.00  --sup_indices_passive                   []
% 2.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_full_bw                           [BwDemod]
% 2.97/1.00  --sup_immed_triv                        [TrivRules]
% 2.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_immed_bw_main                     []
% 2.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  
% 2.97/1.00  ------ Combination Options
% 2.97/1.00  
% 2.97/1.00  --comb_res_mult                         3
% 2.97/1.00  --comb_sup_mult                         2
% 2.97/1.00  --comb_inst_mult                        10
% 2.97/1.00  
% 2.97/1.00  ------ Debug Options
% 2.97/1.00  
% 2.97/1.00  --dbg_backtrace                         false
% 2.97/1.00  --dbg_dump_prop_clauses                 false
% 2.97/1.00  --dbg_dump_prop_clauses_file            -
% 2.97/1.00  --dbg_out_stat                          false
% 2.97/1.00  ------ Parsing...
% 2.97/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.00  ------ Proving...
% 2.97/1.00  ------ Problem Properties 
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  clauses                                 24
% 2.97/1.00  conjectures                             3
% 2.97/1.00  EPR                                     2
% 2.97/1.00  Horn                                    23
% 2.97/1.00  unary                                   13
% 2.97/1.00  binary                                  7
% 2.97/1.00  lits                                    45
% 2.97/1.00  lits eq                                 18
% 2.97/1.00  fd_pure                                 0
% 2.97/1.00  fd_pseudo                               0
% 2.97/1.00  fd_cond                                 2
% 2.97/1.00  fd_pseudo_cond                          1
% 2.97/1.00  AC symbols                              0
% 2.97/1.00  
% 2.97/1.00  ------ Schedule dynamic 5 is on 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  Current options:
% 2.97/1.00  ------ 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options
% 2.97/1.00  
% 2.97/1.00  --out_options                           all
% 2.97/1.00  --tptp_safe_out                         true
% 2.97/1.00  --problem_path                          ""
% 2.97/1.00  --include_path                          ""
% 2.97/1.00  --clausifier                            res/vclausify_rel
% 2.97/1.00  --clausifier_options                    --mode clausify
% 2.97/1.00  --stdin                                 false
% 2.97/1.00  --stats_out                             all
% 2.97/1.00  
% 2.97/1.00  ------ General Options
% 2.97/1.00  
% 2.97/1.00  --fof                                   false
% 2.97/1.00  --time_out_real                         305.
% 2.97/1.00  --time_out_virtual                      -1.
% 2.97/1.00  --symbol_type_check                     false
% 2.97/1.00  --clausify_out                          false
% 2.97/1.00  --sig_cnt_out                           false
% 2.97/1.00  --trig_cnt_out                          false
% 2.97/1.00  --trig_cnt_out_tolerance                1.
% 2.97/1.00  --trig_cnt_out_sk_spl                   false
% 2.97/1.00  --abstr_cl_out                          false
% 2.97/1.00  
% 2.97/1.00  ------ Global Options
% 2.97/1.00  
% 2.97/1.00  --schedule                              default
% 2.97/1.00  --add_important_lit                     false
% 2.97/1.00  --prop_solver_per_cl                    1000
% 2.97/1.00  --min_unsat_core                        false
% 2.97/1.00  --soft_assumptions                      false
% 2.97/1.00  --soft_lemma_size                       3
% 2.97/1.00  --prop_impl_unit_size                   0
% 2.97/1.00  --prop_impl_unit                        []
% 2.97/1.00  --share_sel_clauses                     true
% 2.97/1.00  --reset_solvers                         false
% 2.97/1.00  --bc_imp_inh                            [conj_cone]
% 2.97/1.00  --conj_cone_tolerance                   3.
% 2.97/1.00  --extra_neg_conj                        none
% 2.97/1.00  --large_theory_mode                     true
% 2.97/1.00  --prolific_symb_bound                   200
% 2.97/1.00  --lt_threshold                          2000
% 2.97/1.00  --clause_weak_htbl                      true
% 2.97/1.00  --gc_record_bc_elim                     false
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing Options
% 2.97/1.00  
% 2.97/1.00  --preprocessing_flag                    true
% 2.97/1.00  --time_out_prep_mult                    0.1
% 2.97/1.00  --splitting_mode                        input
% 2.97/1.00  --splitting_grd                         true
% 2.97/1.00  --splitting_cvd                         false
% 2.97/1.00  --splitting_cvd_svl                     false
% 2.97/1.00  --splitting_nvd                         32
% 2.97/1.00  --sub_typing                            true
% 2.97/1.00  --prep_gs_sim                           true
% 2.97/1.00  --prep_unflatten                        true
% 2.97/1.00  --prep_res_sim                          true
% 2.97/1.00  --prep_upred                            true
% 2.97/1.00  --prep_sem_filter                       exhaustive
% 2.97/1.00  --prep_sem_filter_out                   false
% 2.97/1.00  --pred_elim                             true
% 2.97/1.00  --res_sim_input                         true
% 2.97/1.00  --eq_ax_congr_red                       true
% 2.97/1.00  --pure_diseq_elim                       true
% 2.97/1.00  --brand_transform                       false
% 2.97/1.00  --non_eq_to_eq                          false
% 2.97/1.00  --prep_def_merge                        true
% 2.97/1.00  --prep_def_merge_prop_impl              false
% 2.97/1.00  --prep_def_merge_mbd                    true
% 2.97/1.00  --prep_def_merge_tr_red                 false
% 2.97/1.00  --prep_def_merge_tr_cl                  false
% 2.97/1.00  --smt_preprocessing                     true
% 2.97/1.00  --smt_ac_axioms                         fast
% 2.97/1.00  --preprocessed_out                      false
% 2.97/1.00  --preprocessed_stats                    false
% 2.97/1.00  
% 2.97/1.00  ------ Abstraction refinement Options
% 2.97/1.00  
% 2.97/1.00  --abstr_ref                             []
% 2.97/1.00  --abstr_ref_prep                        false
% 2.97/1.00  --abstr_ref_until_sat                   false
% 2.97/1.00  --abstr_ref_sig_restrict                funpre
% 2.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.00  --abstr_ref_under                       []
% 2.97/1.00  
% 2.97/1.00  ------ SAT Options
% 2.97/1.00  
% 2.97/1.00  --sat_mode                              false
% 2.97/1.00  --sat_fm_restart_options                ""
% 2.97/1.00  --sat_gr_def                            false
% 2.97/1.00  --sat_epr_types                         true
% 2.97/1.00  --sat_non_cyclic_types                  false
% 2.97/1.00  --sat_finite_models                     false
% 2.97/1.00  --sat_fm_lemmas                         false
% 2.97/1.00  --sat_fm_prep                           false
% 2.97/1.00  --sat_fm_uc_incr                        true
% 2.97/1.00  --sat_out_model                         small
% 2.97/1.00  --sat_out_clauses                       false
% 2.97/1.00  
% 2.97/1.00  ------ QBF Options
% 2.97/1.00  
% 2.97/1.00  --qbf_mode                              false
% 2.97/1.00  --qbf_elim_univ                         false
% 2.97/1.00  --qbf_dom_inst                          none
% 2.97/1.00  --qbf_dom_pre_inst                      false
% 2.97/1.00  --qbf_sk_in                             false
% 2.97/1.00  --qbf_pred_elim                         true
% 2.97/1.00  --qbf_split                             512
% 2.97/1.00  
% 2.97/1.00  ------ BMC1 Options
% 2.97/1.00  
% 2.97/1.00  --bmc1_incremental                      false
% 2.97/1.00  --bmc1_axioms                           reachable_all
% 2.97/1.00  --bmc1_min_bound                        0
% 2.97/1.00  --bmc1_max_bound                        -1
% 2.97/1.00  --bmc1_max_bound_default                -1
% 2.97/1.00  --bmc1_symbol_reachability              true
% 2.97/1.00  --bmc1_property_lemmas                  false
% 2.97/1.00  --bmc1_k_induction                      false
% 2.97/1.00  --bmc1_non_equiv_states                 false
% 2.97/1.00  --bmc1_deadlock                         false
% 2.97/1.00  --bmc1_ucm                              false
% 2.97/1.00  --bmc1_add_unsat_core                   none
% 2.97/1.00  --bmc1_unsat_core_children              false
% 2.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.00  --bmc1_out_stat                         full
% 2.97/1.00  --bmc1_ground_init                      false
% 2.97/1.00  --bmc1_pre_inst_next_state              false
% 2.97/1.00  --bmc1_pre_inst_state                   false
% 2.97/1.00  --bmc1_pre_inst_reach_state             false
% 2.97/1.00  --bmc1_out_unsat_core                   false
% 2.97/1.00  --bmc1_aig_witness_out                  false
% 2.97/1.00  --bmc1_verbose                          false
% 2.97/1.00  --bmc1_dump_clauses_tptp                false
% 2.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.00  --bmc1_dump_file                        -
% 2.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.00  --bmc1_ucm_extend_mode                  1
% 2.97/1.00  --bmc1_ucm_init_mode                    2
% 2.97/1.00  --bmc1_ucm_cone_mode                    none
% 2.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.00  --bmc1_ucm_relax_model                  4
% 2.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.00  --bmc1_ucm_layered_model                none
% 2.97/1.00  --bmc1_ucm_max_lemma_size               10
% 2.97/1.00  
% 2.97/1.00  ------ AIG Options
% 2.97/1.00  
% 2.97/1.00  --aig_mode                              false
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation Options
% 2.97/1.00  
% 2.97/1.00  --instantiation_flag                    true
% 2.97/1.00  --inst_sos_flag                         false
% 2.97/1.00  --inst_sos_phase                        true
% 2.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel_side                     none
% 2.97/1.00  --inst_solver_per_active                1400
% 2.97/1.00  --inst_solver_calls_frac                1.
% 2.97/1.00  --inst_passive_queue_type               priority_queues
% 2.97/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.00  --inst_passive_queues_freq              [25;2]
% 2.97/1.00  --inst_dismatching                      true
% 2.97/1.00  --inst_eager_unprocessed_to_passive     true
% 2.97/1.00  --inst_prop_sim_given                   true
% 2.97/1.00  --inst_prop_sim_new                     false
% 2.97/1.00  --inst_subs_new                         false
% 2.97/1.00  --inst_eq_res_simp                      false
% 2.97/1.00  --inst_subs_given                       false
% 2.97/1.00  --inst_orphan_elimination               true
% 2.97/1.00  --inst_learning_loop_flag               true
% 2.97/1.00  --inst_learning_start                   3000
% 2.97/1.00  --inst_learning_factor                  2
% 2.97/1.00  --inst_start_prop_sim_after_learn       3
% 2.97/1.00  --inst_sel_renew                        solver
% 2.97/1.00  --inst_lit_activity_flag                true
% 2.97/1.00  --inst_restr_to_given                   false
% 2.97/1.00  --inst_activity_threshold               500
% 2.97/1.00  --inst_out_proof                        true
% 2.97/1.00  
% 2.97/1.00  ------ Resolution Options
% 2.97/1.00  
% 2.97/1.00  --resolution_flag                       false
% 2.97/1.00  --res_lit_sel                           adaptive
% 2.97/1.00  --res_lit_sel_side                      none
% 2.97/1.00  --res_ordering                          kbo
% 2.97/1.00  --res_to_prop_solver                    active
% 2.97/1.00  --res_prop_simpl_new                    false
% 2.97/1.00  --res_prop_simpl_given                  true
% 2.97/1.00  --res_passive_queue_type                priority_queues
% 2.97/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.00  --res_passive_queues_freq               [15;5]
% 2.97/1.00  --res_forward_subs                      full
% 2.97/1.00  --res_backward_subs                     full
% 2.97/1.00  --res_forward_subs_resolution           true
% 2.97/1.00  --res_backward_subs_resolution          true
% 2.97/1.00  --res_orphan_elimination                true
% 2.97/1.00  --res_time_limit                        2.
% 2.97/1.00  --res_out_proof                         true
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Options
% 2.97/1.00  
% 2.97/1.00  --superposition_flag                    true
% 2.97/1.00  --sup_passive_queue_type                priority_queues
% 2.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.00  --demod_completeness_check              fast
% 2.97/1.00  --demod_use_ground                      true
% 2.97/1.00  --sup_to_prop_solver                    passive
% 2.97/1.00  --sup_prop_simpl_new                    true
% 2.97/1.00  --sup_prop_simpl_given                  true
% 2.97/1.00  --sup_fun_splitting                     false
% 2.97/1.00  --sup_smt_interval                      50000
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Simplification Setup
% 2.97/1.00  
% 2.97/1.00  --sup_indices_passive                   []
% 2.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_full_bw                           [BwDemod]
% 2.97/1.00  --sup_immed_triv                        [TrivRules]
% 2.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_immed_bw_main                     []
% 2.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  
% 2.97/1.00  ------ Combination Options
% 2.97/1.00  
% 2.97/1.00  --comb_res_mult                         3
% 2.97/1.00  --comb_sup_mult                         2
% 2.97/1.00  --comb_inst_mult                        10
% 2.97/1.00  
% 2.97/1.00  ------ Debug Options
% 2.97/1.00  
% 2.97/1.00  --dbg_backtrace                         false
% 2.97/1.00  --dbg_dump_prop_clauses                 false
% 2.97/1.00  --dbg_dump_prop_clauses_file            -
% 2.97/1.00  --dbg_out_stat                          false
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ Proving...
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS status Theorem for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00   Resolution empty clause
% 2.97/1.00  
% 2.97/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  fof(f15,conjecture,(
% 2.97/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f16,negated_conjecture,(
% 2.97/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.97/1.00    inference(negated_conjecture,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f17,plain,(
% 2.97/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.97/1.00    inference(pure_predicate_removal,[],[f16])).
% 2.97/1.00  
% 2.97/1.00  fof(f28,plain,(
% 2.97/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.97/1.00    inference(ennf_transformation,[],[f17])).
% 2.97/1.00  
% 2.97/1.00  fof(f29,plain,(
% 2.97/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.97/1.00    inference(flattening,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  fof(f33,plain,(
% 2.97/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f34,plain,(
% 2.97/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f33])).
% 2.97/1.00  
% 2.97/1.00  fof(f60,plain,(
% 2.97/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.97/1.00    inference(cnf_transformation,[],[f34])).
% 2.97/1.00  
% 2.97/1.00  fof(f2,axiom,(
% 2.97/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f36,plain,(
% 2.97/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f2])).
% 2.97/1.00  
% 2.97/1.00  fof(f3,axiom,(
% 2.97/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f37,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f3])).
% 2.97/1.00  
% 2.97/1.00  fof(f4,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f38,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f4])).
% 2.97/1.00  
% 2.97/1.00  fof(f63,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.97/1.00    inference(definition_unfolding,[],[f37,f38])).
% 2.97/1.00  
% 2.97/1.00  fof(f64,plain,(
% 2.97/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.97/1.00    inference(definition_unfolding,[],[f36,f63])).
% 2.97/1.00  
% 2.97/1.00  fof(f76,plain,(
% 2.97/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.97/1.00    inference(definition_unfolding,[],[f60,f64])).
% 2.97/1.00  
% 2.97/1.00  fof(f13,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f26,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(ennf_transformation,[],[f13])).
% 2.97/1.00  
% 2.97/1.00  fof(f57,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f26])).
% 2.97/1.00  
% 2.97/1.00  fof(f12,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f25,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(ennf_transformation,[],[f12])).
% 2.97/1.00  
% 2.97/1.00  fof(f56,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f25])).
% 2.97/1.00  
% 2.97/1.00  fof(f6,axiom,(
% 2.97/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f32,plain,(
% 2.97/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.97/1.00    inference(nnf_transformation,[],[f6])).
% 2.97/1.00  
% 2.97/1.00  fof(f48,plain,(
% 2.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f32])).
% 2.97/1.00  
% 2.97/1.00  fof(f5,axiom,(
% 2.97/1.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f18,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.97/1.00    inference(ennf_transformation,[],[f5])).
% 2.97/1.00  
% 2.97/1.00  fof(f30,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.97/1.00    inference(nnf_transformation,[],[f18])).
% 2.97/1.00  
% 2.97/1.00  fof(f31,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.97/1.00    inference(flattening,[],[f30])).
% 2.97/1.00  
% 2.97/1.00  fof(f39,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f31])).
% 2.97/1.00  
% 2.97/1.00  fof(f73,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.97/1.00    inference(definition_unfolding,[],[f39,f38,f63,f63,f63,f64,f64,f64,f38])).
% 2.97/1.00  
% 2.97/1.00  fof(f10,axiom,(
% 2.97/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f22,plain,(
% 2.97/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.97/1.00    inference(ennf_transformation,[],[f10])).
% 2.97/1.00  
% 2.97/1.00  fof(f23,plain,(
% 2.97/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.97/1.00    inference(flattening,[],[f22])).
% 2.97/1.00  
% 2.97/1.00  fof(f54,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f74,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.97/1.00    inference(definition_unfolding,[],[f54,f64,f64])).
% 2.97/1.00  
% 2.97/1.00  fof(f59,plain,(
% 2.97/1.00    v1_funct_1(sK3)),
% 2.97/1.00    inference(cnf_transformation,[],[f34])).
% 2.97/1.00  
% 2.97/1.00  fof(f11,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f24,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(ennf_transformation,[],[f11])).
% 2.97/1.00  
% 2.97/1.00  fof(f55,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f24])).
% 2.97/1.00  
% 2.97/1.00  fof(f7,axiom,(
% 2.97/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f19,plain,(
% 2.97/1.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.97/1.00    inference(ennf_transformation,[],[f7])).
% 2.97/1.00  
% 2.97/1.00  fof(f50,plain,(
% 2.97/1.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f19])).
% 2.97/1.00  
% 2.97/1.00  fof(f14,axiom,(
% 2.97/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f27,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(ennf_transformation,[],[f14])).
% 2.97/1.00  
% 2.97/1.00  fof(f58,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f27])).
% 2.97/1.00  
% 2.97/1.00  fof(f62,plain,(
% 2.97/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.97/1.00    inference(cnf_transformation,[],[f34])).
% 2.97/1.00  
% 2.97/1.00  fof(f75,plain,(
% 2.97/1.00    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.97/1.00    inference(definition_unfolding,[],[f62,f64,f64])).
% 2.97/1.00  
% 2.97/1.00  fof(f9,axiom,(
% 2.97/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f20,plain,(
% 2.97/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f9])).
% 2.97/1.00  
% 2.97/1.00  fof(f21,plain,(
% 2.97/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.97/1.00    inference(flattening,[],[f20])).
% 2.97/1.00  
% 2.97/1.00  fof(f52,plain,(
% 2.97/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f21])).
% 2.97/1.00  
% 2.97/1.00  fof(f8,axiom,(
% 2.97/1.00    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f51,plain,(
% 2.97/1.00    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f8])).
% 2.97/1.00  
% 2.97/1.00  fof(f1,axiom,(
% 2.97/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f35,plain,(
% 2.97/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f1])).
% 2.97/1.00  
% 2.97/1.00  cnf(c_23,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2159,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_19,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2162,plain,
% 2.97/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.97/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3071,plain,
% 2.97/1.00      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2159,c_2162]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_18,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2163,plain,
% 2.97/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3199,plain,
% 2.97/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top
% 2.97/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3071,c_2163]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_26,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3388,plain,
% 2.97/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3199,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_11,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2168,plain,
% 2.97/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.97/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3393,plain,
% 2.97/1.00      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3388,c_2168]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_9,plain,
% 2.97/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.97/1.00      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.97/1.00      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.97/1.00      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.97/1.00      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.97/1.00      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.97/1.00      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.97/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.97/1.00      | k1_xboole_0 = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2170,plain,
% 2.97/1.00      ( k2_enumset1(X0,X0,X1,X2) = X3
% 2.97/1.00      | k2_enumset1(X0,X0,X0,X2) = X3
% 2.97/1.00      | k2_enumset1(X1,X1,X1,X2) = X3
% 2.97/1.00      | k2_enumset1(X0,X0,X0,X1) = X3
% 2.97/1.00      | k2_enumset1(X2,X2,X2,X2) = X3
% 2.97/1.00      | k2_enumset1(X1,X1,X1,X1) = X3
% 2.97/1.00      | k2_enumset1(X0,X0,X0,X0) = X3
% 2.97/1.00      | k1_xboole_0 = X3
% 2.97/1.00      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3716,plain,
% 2.97/1.00      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.97/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3393,c_2170]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_16,plain,
% 2.97/1.00      ( ~ v1_funct_1(X0)
% 2.97/1.00      | ~ v1_relat_1(X0)
% 2.97/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.97/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_24,negated_conjecture,
% 2.97/1.00      ( v1_funct_1(sK3) ),
% 2.97/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_302,plain,
% 2.97/1.00      ( ~ v1_relat_1(X0)
% 2.97/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.97/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.97/1.00      | sK3 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_303,plain,
% 2.97/1.00      ( ~ v1_relat_1(sK3)
% 2.97/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.97/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_302]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2158,plain,
% 2.97/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.97/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.97/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_304,plain,
% 2.97/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.97/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.97/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_17,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2324,plain,
% 2.97/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.97/1.00      | v1_relat_1(sK3) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2325,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 2.97/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2324]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2332,plain,
% 2.97/1.00      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.97/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_2158,c_26,c_304,c_2325]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2333,plain,
% 2.97/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.97/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_2332]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3736,plain,
% 2.97/1.00      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.97/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3716,c_2333]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4235,plain,
% 2.97/1.00      ( k2_enumset1(k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0))) = k2_relat_1(sK3)
% 2.97/1.00      | k1_relat_1(sK3) != k2_relat_1(sK3)
% 2.97/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3736,c_2333]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_12,plain,
% 2.97/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2167,plain,
% 2.97/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 2.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_20,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.97/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2161,plain,
% 2.97/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.97/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3180,plain,
% 2.97/1.00      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2159,c_2161]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_21,negated_conjecture,
% 2.97/1.00      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2160,plain,
% 2.97/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3265,plain,
% 2.97/1.00      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_3180,c_2160]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4238,plain,
% 2.97/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 2.97/1.00      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3736,c_3265]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4295,plain,
% 2.97/1.00      ( k1_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2167,c_4238]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4363,plain,
% 2.97/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_4235,c_26,c_2325,c_4295]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_15,plain,
% 2.97/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2165,plain,
% 2.97/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 2.97/1.00      | k1_xboole_0 = X0
% 2.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4384,plain,
% 2.97/1.00      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_4363,c_2165]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2444,plain,
% 2.97/1.00      ( ~ v1_relat_1(sK3)
% 2.97/1.00      | k1_relat_1(sK3) != k1_xboole_0
% 2.97/1.00      | k1_xboole_0 = sK3 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1638,plain,( X0 = X0 ),theory(equality) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2483,plain,
% 2.97/1.00      ( sK3 = sK3 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1638]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1639,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2774,plain,
% 2.97/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1639]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2959,plain,
% 2.97/1.00      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2774]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4301,plain,
% 2.97/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2959]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4471,plain,
% 2.97/1.00      ( sK3 = k1_xboole_0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_4384,c_23,c_26,c_2324,c_2325,c_2444,c_2483,c_4295,c_4301]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4477,plain,
% 2.97/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_4471,c_3265]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_13,plain,
% 2.97/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4489,plain,
% 2.97/1.00      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_4477,c_13]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_0,plain,
% 2.97/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2179,plain,
% 2.97/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4627,plain,
% 2.97/1.00      ( $false ),
% 2.97/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4489,c_2179]) ).
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  ------                               Statistics
% 2.97/1.00  
% 2.97/1.00  ------ General
% 2.97/1.00  
% 2.97/1.00  abstr_ref_over_cycles:                  0
% 2.97/1.00  abstr_ref_under_cycles:                 0
% 2.97/1.00  gc_basic_clause_elim:                   0
% 2.97/1.00  forced_gc_time:                         0
% 2.97/1.00  parsing_time:                           0.008
% 2.97/1.00  unif_index_cands_time:                  0.
% 2.97/1.00  unif_index_add_time:                    0.
% 2.97/1.00  orderings_time:                         0.
% 2.97/1.00  out_proof_time:                         0.011
% 2.97/1.00  total_time:                             0.182
% 2.97/1.00  num_of_symbols:                         49
% 2.97/1.00  num_of_terms:                           4170
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing
% 2.97/1.00  
% 2.97/1.00  num_of_splits:                          0
% 2.97/1.00  num_of_split_atoms:                     0
% 2.97/1.00  num_of_reused_defs:                     0
% 2.97/1.00  num_eq_ax_congr_red:                    15
% 2.97/1.00  num_of_sem_filtered_clauses:            1
% 2.97/1.00  num_of_subtypes:                        0
% 2.97/1.00  monotx_restored_types:                  0
% 2.97/1.00  sat_num_of_epr_types:                   0
% 2.97/1.00  sat_num_of_non_cyclic_types:            0
% 2.97/1.00  sat_guarded_non_collapsed_types:        0
% 2.97/1.00  num_pure_diseq_elim:                    0
% 2.97/1.00  simp_replaced_by:                       0
% 2.97/1.00  res_preprocessed:                       124
% 2.97/1.00  prep_upred:                             0
% 2.97/1.00  prep_unflattend:                        75
% 2.97/1.00  smt_new_axioms:                         0
% 2.97/1.00  pred_elim_cands:                        3
% 2.97/1.00  pred_elim:                              1
% 2.97/1.00  pred_elim_cl:                           1
% 2.97/1.00  pred_elim_cycles:                       5
% 2.97/1.00  merged_defs:                            8
% 2.97/1.00  merged_defs_ncl:                        0
% 2.97/1.00  bin_hyper_res:                          8
% 2.97/1.00  prep_cycles:                            4
% 2.97/1.00  pred_elim_time:                         0.019
% 2.97/1.00  splitting_time:                         0.
% 2.97/1.00  sem_filter_time:                        0.
% 2.97/1.00  monotx_time:                            0.001
% 2.97/1.00  subtype_inf_time:                       0.
% 2.97/1.00  
% 2.97/1.00  ------ Problem properties
% 2.97/1.00  
% 2.97/1.00  clauses:                                24
% 2.97/1.00  conjectures:                            3
% 2.97/1.00  epr:                                    2
% 2.97/1.00  horn:                                   23
% 2.97/1.00  ground:                                 3
% 2.97/1.00  unary:                                  13
% 2.97/1.00  binary:                                 7
% 2.97/1.00  lits:                                   45
% 2.97/1.00  lits_eq:                                18
% 2.97/1.00  fd_pure:                                0
% 2.97/1.00  fd_pseudo:                              0
% 2.97/1.00  fd_cond:                                2
% 2.97/1.00  fd_pseudo_cond:                         1
% 2.97/1.00  ac_symbols:                             0
% 2.97/1.00  
% 2.97/1.00  ------ Propositional Solver
% 2.97/1.00  
% 2.97/1.00  prop_solver_calls:                      28
% 2.97/1.00  prop_fast_solver_calls:                 846
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    1060
% 2.97/1.00  prop_preprocess_simplified:             5208
% 2.97/1.00  prop_fo_subsumed:                       5
% 2.97/1.00  prop_solver_time:                       0.
% 2.97/1.00  smt_solver_time:                        0.
% 2.97/1.00  smt_fast_solver_time:                   0.
% 2.97/1.00  prop_fast_solver_time:                  0.
% 2.97/1.00  prop_unsat_core_time:                   0.
% 2.97/1.00  
% 2.97/1.00  ------ QBF
% 2.97/1.00  
% 2.97/1.00  qbf_q_res:                              0
% 2.97/1.00  qbf_num_tautologies:                    0
% 2.97/1.00  qbf_prep_cycles:                        0
% 2.97/1.00  
% 2.97/1.00  ------ BMC1
% 2.97/1.00  
% 2.97/1.00  bmc1_current_bound:                     -1
% 2.97/1.00  bmc1_last_solved_bound:                 -1
% 2.97/1.00  bmc1_unsat_core_size:                   -1
% 2.97/1.00  bmc1_unsat_core_parents_size:           -1
% 2.97/1.00  bmc1_merge_next_fun:                    0
% 2.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation
% 2.97/1.00  
% 2.97/1.00  inst_num_of_clauses:                    358
% 2.97/1.00  inst_num_in_passive:                    67
% 2.97/1.00  inst_num_in_active:                     242
% 2.97/1.00  inst_num_in_unprocessed:                49
% 2.97/1.00  inst_num_of_loops:                      250
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          5
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                0
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      345
% 2.97/1.00  inst_num_of_non_proper_insts:           452
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       128
% 2.97/1.00  res_forward_subset_subsumed:            84
% 2.97/1.00  res_backward_subset_subsumed:           2
% 2.97/1.00  res_forward_subsumed:                   2
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     0
% 2.97/1.00  res_backward_subsumption_resolution:    0
% 2.97/1.00  res_clause_to_clause_subsumption:       377
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      101
% 2.97/1.00  res_num_eq_res_simplified:              0
% 2.97/1.00  res_num_sel_changes:                    0
% 2.97/1.00  res_moves_from_active_to_pass:          0
% 2.97/1.00  
% 2.97/1.00  ------ Superposition
% 2.97/1.00  
% 2.97/1.00  sup_time_total:                         0.
% 2.97/1.00  sup_time_generating:                    0.
% 2.97/1.00  sup_time_sim_full:                      0.
% 2.97/1.00  sup_time_sim_immed:                     0.
% 2.97/1.00  
% 2.97/1.00  sup_num_of_clauses:                     45
% 2.97/1.00  sup_num_in_active:                      28
% 2.97/1.00  sup_num_in_passive:                     17
% 2.97/1.00  sup_num_of_loops:                       49
% 2.97/1.00  sup_fw_superposition:                   32
% 2.97/1.00  sup_bw_superposition:                   55
% 2.97/1.00  sup_immediate_simplified:               17
% 2.97/1.00  sup_given_eliminated:                   0
% 2.97/1.00  comparisons_done:                       0
% 2.97/1.00  comparisons_avoided:                    6
% 2.97/1.00  
% 2.97/1.00  ------ Simplifications
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  sim_fw_subset_subsumed:                 4
% 2.97/1.00  sim_bw_subset_subsumed:                 16
% 2.97/1.00  sim_fw_subsumed:                        10
% 2.97/1.00  sim_bw_subsumed:                        1
% 2.97/1.00  sim_fw_subsumption_res:                 1
% 2.97/1.00  sim_bw_subsumption_res:                 0
% 2.97/1.00  sim_tautology_del:                      1
% 2.97/1.00  sim_eq_tautology_del:                   11
% 2.97/1.00  sim_eq_res_simp:                        0
% 2.97/1.00  sim_fw_demodulated:                     1
% 2.97/1.00  sim_bw_demodulated:                     16
% 2.97/1.00  sim_light_normalised:                   2
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------
