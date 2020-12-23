%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:33 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 442 expanded)
%              Number of clauses        :   60 ( 114 expanded)
%              Number of leaves         :   16 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          :  296 (1099 expanded)
%              Number of equality atoms :  130 ( 431 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
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

fof(f37,plain,
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

fof(f38,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f37])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f44,f63,f63])).

fof(f62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f62,f63,f63])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f63,f63])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_enumset1(X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f73,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f65])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_299,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_295,c_15])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_299])).

cnf(c_1323,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_1706,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1323])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1335,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2657,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1706,c_1335])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_276,plain,
    ( ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_277,plain,
    ( ~ v1_relat_1(sK3)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_278,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_280,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_enumset1(sK0,sK0,sK0) != k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_1463,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1464,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1504,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1590,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_899,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1485,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_1589,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_1680,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_11,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1537,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1681,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_2959,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2657,c_20,c_23,c_18,c_280,c_1463,c_1464,c_1590,c_1680,c_1681])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1329,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2974,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2959,c_1329])).

cnf(c_1538,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3114,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2974,c_20,c_23,c_18,c_280,c_1463,c_1464,c_1538,c_1590,c_1680,c_1681,c_2657])).

cnf(c_1331,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3120,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3114,c_1331])).

cnf(c_3517,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3120,c_23,c_1464])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1334,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1332,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1620,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1332])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1339,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2415,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1339])).

cnf(c_3525,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3517,c_2415])).

cnf(c_1327,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2464,plain,
    ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1325,c_1327])).

cnf(c_1326,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2773,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2464,c_1326])).

cnf(c_3535,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3525,c_2773])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2171,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2174,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3535,c_2174])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.23/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.07  
% 2.23/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.23/1.07  
% 2.23/1.07  ------  iProver source info
% 2.23/1.07  
% 2.23/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.23/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.23/1.07  git: non_committed_changes: false
% 2.23/1.07  git: last_make_outside_of_git: false
% 2.23/1.07  
% 2.23/1.07  ------ 
% 2.23/1.07  
% 2.23/1.07  ------ Input Options
% 2.23/1.07  
% 2.23/1.07  --out_options                           all
% 2.23/1.07  --tptp_safe_out                         true
% 2.23/1.07  --problem_path                          ""
% 2.23/1.07  --include_path                          ""
% 2.23/1.07  --clausifier                            res/vclausify_rel
% 2.23/1.07  --clausifier_options                    --mode clausify
% 2.23/1.07  --stdin                                 false
% 2.23/1.07  --stats_out                             all
% 2.23/1.07  
% 2.23/1.07  ------ General Options
% 2.23/1.07  
% 2.23/1.07  --fof                                   false
% 2.23/1.07  --time_out_real                         305.
% 2.23/1.07  --time_out_virtual                      -1.
% 2.23/1.07  --symbol_type_check                     false
% 2.23/1.07  --clausify_out                          false
% 2.23/1.07  --sig_cnt_out                           false
% 2.23/1.07  --trig_cnt_out                          false
% 2.23/1.07  --trig_cnt_out_tolerance                1.
% 2.23/1.07  --trig_cnt_out_sk_spl                   false
% 2.23/1.07  --abstr_cl_out                          false
% 2.23/1.07  
% 2.23/1.07  ------ Global Options
% 2.23/1.07  
% 2.23/1.07  --schedule                              default
% 2.23/1.07  --add_important_lit                     false
% 2.23/1.07  --prop_solver_per_cl                    1000
% 2.23/1.07  --min_unsat_core                        false
% 2.23/1.07  --soft_assumptions                      false
% 2.23/1.07  --soft_lemma_size                       3
% 2.23/1.07  --prop_impl_unit_size                   0
% 2.23/1.07  --prop_impl_unit                        []
% 2.23/1.07  --share_sel_clauses                     true
% 2.23/1.07  --reset_solvers                         false
% 2.23/1.07  --bc_imp_inh                            [conj_cone]
% 2.23/1.07  --conj_cone_tolerance                   3.
% 2.23/1.07  --extra_neg_conj                        none
% 2.23/1.07  --large_theory_mode                     true
% 2.23/1.07  --prolific_symb_bound                   200
% 2.23/1.07  --lt_threshold                          2000
% 2.23/1.07  --clause_weak_htbl                      true
% 2.23/1.07  --gc_record_bc_elim                     false
% 2.23/1.07  
% 2.23/1.07  ------ Preprocessing Options
% 2.23/1.07  
% 2.23/1.07  --preprocessing_flag                    true
% 2.23/1.07  --time_out_prep_mult                    0.1
% 2.23/1.07  --splitting_mode                        input
% 2.23/1.07  --splitting_grd                         true
% 2.23/1.07  --splitting_cvd                         false
% 2.23/1.07  --splitting_cvd_svl                     false
% 2.23/1.07  --splitting_nvd                         32
% 2.23/1.07  --sub_typing                            true
% 2.23/1.07  --prep_gs_sim                           true
% 2.23/1.07  --prep_unflatten                        true
% 2.23/1.07  --prep_res_sim                          true
% 2.23/1.07  --prep_upred                            true
% 2.23/1.07  --prep_sem_filter                       exhaustive
% 2.23/1.07  --prep_sem_filter_out                   false
% 2.23/1.07  --pred_elim                             true
% 2.23/1.07  --res_sim_input                         true
% 2.23/1.07  --eq_ax_congr_red                       true
% 2.23/1.07  --pure_diseq_elim                       true
% 2.23/1.07  --brand_transform                       false
% 2.23/1.07  --non_eq_to_eq                          false
% 2.23/1.07  --prep_def_merge                        true
% 2.23/1.07  --prep_def_merge_prop_impl              false
% 2.23/1.07  --prep_def_merge_mbd                    true
% 2.23/1.07  --prep_def_merge_tr_red                 false
% 2.23/1.07  --prep_def_merge_tr_cl                  false
% 2.23/1.07  --smt_preprocessing                     true
% 2.23/1.07  --smt_ac_axioms                         fast
% 2.23/1.07  --preprocessed_out                      false
% 2.23/1.07  --preprocessed_stats                    false
% 2.23/1.07  
% 2.23/1.07  ------ Abstraction refinement Options
% 2.23/1.07  
% 2.23/1.07  --abstr_ref                             []
% 2.23/1.07  --abstr_ref_prep                        false
% 2.23/1.07  --abstr_ref_until_sat                   false
% 2.23/1.07  --abstr_ref_sig_restrict                funpre
% 2.23/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/1.07  --abstr_ref_under                       []
% 2.23/1.07  
% 2.23/1.07  ------ SAT Options
% 2.23/1.07  
% 2.23/1.07  --sat_mode                              false
% 2.23/1.07  --sat_fm_restart_options                ""
% 2.23/1.07  --sat_gr_def                            false
% 2.23/1.07  --sat_epr_types                         true
% 2.23/1.07  --sat_non_cyclic_types                  false
% 2.23/1.07  --sat_finite_models                     false
% 2.23/1.07  --sat_fm_lemmas                         false
% 2.23/1.07  --sat_fm_prep                           false
% 2.23/1.07  --sat_fm_uc_incr                        true
% 2.23/1.07  --sat_out_model                         small
% 2.23/1.07  --sat_out_clauses                       false
% 2.23/1.07  
% 2.23/1.07  ------ QBF Options
% 2.23/1.07  
% 2.23/1.07  --qbf_mode                              false
% 2.23/1.07  --qbf_elim_univ                         false
% 2.23/1.07  --qbf_dom_inst                          none
% 2.23/1.07  --qbf_dom_pre_inst                      false
% 2.23/1.07  --qbf_sk_in                             false
% 2.23/1.07  --qbf_pred_elim                         true
% 2.23/1.07  --qbf_split                             512
% 2.23/1.07  
% 2.23/1.07  ------ BMC1 Options
% 2.23/1.07  
% 2.23/1.07  --bmc1_incremental                      false
% 2.23/1.07  --bmc1_axioms                           reachable_all
% 2.23/1.07  --bmc1_min_bound                        0
% 2.23/1.07  --bmc1_max_bound                        -1
% 2.23/1.07  --bmc1_max_bound_default                -1
% 2.23/1.07  --bmc1_symbol_reachability              true
% 2.23/1.07  --bmc1_property_lemmas                  false
% 2.23/1.07  --bmc1_k_induction                      false
% 2.23/1.07  --bmc1_non_equiv_states                 false
% 2.23/1.07  --bmc1_deadlock                         false
% 2.23/1.07  --bmc1_ucm                              false
% 2.23/1.07  --bmc1_add_unsat_core                   none
% 2.23/1.07  --bmc1_unsat_core_children              false
% 2.23/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/1.07  --bmc1_out_stat                         full
% 2.23/1.07  --bmc1_ground_init                      false
% 2.23/1.07  --bmc1_pre_inst_next_state              false
% 2.23/1.07  --bmc1_pre_inst_state                   false
% 2.23/1.07  --bmc1_pre_inst_reach_state             false
% 2.23/1.07  --bmc1_out_unsat_core                   false
% 2.23/1.07  --bmc1_aig_witness_out                  false
% 2.23/1.07  --bmc1_verbose                          false
% 2.23/1.07  --bmc1_dump_clauses_tptp                false
% 2.23/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.23/1.07  --bmc1_dump_file                        -
% 2.23/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.23/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.23/1.07  --bmc1_ucm_extend_mode                  1
% 2.23/1.07  --bmc1_ucm_init_mode                    2
% 2.23/1.07  --bmc1_ucm_cone_mode                    none
% 2.23/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.23/1.07  --bmc1_ucm_relax_model                  4
% 2.23/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.23/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/1.07  --bmc1_ucm_layered_model                none
% 2.23/1.07  --bmc1_ucm_max_lemma_size               10
% 2.23/1.07  
% 2.23/1.07  ------ AIG Options
% 2.23/1.07  
% 2.23/1.07  --aig_mode                              false
% 2.23/1.07  
% 2.23/1.07  ------ Instantiation Options
% 2.23/1.07  
% 2.23/1.07  --instantiation_flag                    true
% 2.23/1.07  --inst_sos_flag                         false
% 2.23/1.07  --inst_sos_phase                        true
% 2.23/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/1.07  --inst_lit_sel_side                     num_symb
% 2.23/1.07  --inst_solver_per_active                1400
% 2.23/1.07  --inst_solver_calls_frac                1.
% 2.23/1.07  --inst_passive_queue_type               priority_queues
% 2.23/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/1.07  --inst_passive_queues_freq              [25;2]
% 2.23/1.07  --inst_dismatching                      true
% 2.23/1.07  --inst_eager_unprocessed_to_passive     true
% 2.23/1.07  --inst_prop_sim_given                   true
% 2.23/1.07  --inst_prop_sim_new                     false
% 2.23/1.07  --inst_subs_new                         false
% 2.23/1.07  --inst_eq_res_simp                      false
% 2.23/1.07  --inst_subs_given                       false
% 2.23/1.07  --inst_orphan_elimination               true
% 2.23/1.07  --inst_learning_loop_flag               true
% 2.23/1.07  --inst_learning_start                   3000
% 2.23/1.07  --inst_learning_factor                  2
% 2.23/1.07  --inst_start_prop_sim_after_learn       3
% 2.23/1.07  --inst_sel_renew                        solver
% 2.23/1.07  --inst_lit_activity_flag                true
% 2.23/1.07  --inst_restr_to_given                   false
% 2.23/1.07  --inst_activity_threshold               500
% 2.23/1.07  --inst_out_proof                        true
% 2.23/1.07  
% 2.23/1.07  ------ Resolution Options
% 2.23/1.07  
% 2.23/1.07  --resolution_flag                       true
% 2.23/1.07  --res_lit_sel                           adaptive
% 2.23/1.07  --res_lit_sel_side                      none
% 2.23/1.07  --res_ordering                          kbo
% 2.23/1.07  --res_to_prop_solver                    active
% 2.23/1.07  --res_prop_simpl_new                    false
% 2.23/1.07  --res_prop_simpl_given                  true
% 2.23/1.07  --res_passive_queue_type                priority_queues
% 2.23/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/1.07  --res_passive_queues_freq               [15;5]
% 2.23/1.07  --res_forward_subs                      full
% 2.23/1.07  --res_backward_subs                     full
% 2.23/1.07  --res_forward_subs_resolution           true
% 2.23/1.07  --res_backward_subs_resolution          true
% 2.23/1.07  --res_orphan_elimination                true
% 2.23/1.07  --res_time_limit                        2.
% 2.23/1.07  --res_out_proof                         true
% 2.23/1.07  
% 2.23/1.07  ------ Superposition Options
% 2.23/1.07  
% 2.23/1.07  --superposition_flag                    true
% 2.23/1.07  --sup_passive_queue_type                priority_queues
% 2.23/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.23/1.07  --demod_completeness_check              fast
% 2.23/1.07  --demod_use_ground                      true
% 2.23/1.07  --sup_to_prop_solver                    passive
% 2.23/1.07  --sup_prop_simpl_new                    true
% 2.23/1.07  --sup_prop_simpl_given                  true
% 2.23/1.07  --sup_fun_splitting                     false
% 2.23/1.07  --sup_smt_interval                      50000
% 2.23/1.07  
% 2.23/1.07  ------ Superposition Simplification Setup
% 2.23/1.07  
% 2.23/1.07  --sup_indices_passive                   []
% 2.23/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.07  --sup_full_bw                           [BwDemod]
% 2.23/1.07  --sup_immed_triv                        [TrivRules]
% 2.23/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.07  --sup_immed_bw_main                     []
% 2.23/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.07  
% 2.23/1.07  ------ Combination Options
% 2.23/1.07  
% 2.23/1.07  --comb_res_mult                         3
% 2.23/1.07  --comb_sup_mult                         2
% 2.23/1.07  --comb_inst_mult                        10
% 2.23/1.07  
% 2.23/1.07  ------ Debug Options
% 2.23/1.07  
% 2.23/1.07  --dbg_backtrace                         false
% 2.23/1.07  --dbg_dump_prop_clauses                 false
% 2.23/1.07  --dbg_dump_prop_clauses_file            -
% 2.23/1.07  --dbg_out_stat                          false
% 2.23/1.07  ------ Parsing...
% 2.23/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.23/1.07  
% 2.23/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.23/1.07  
% 2.23/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.23/1.07  
% 2.23/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.23/1.07  ------ Proving...
% 2.23/1.07  ------ Problem Properties 
% 2.23/1.07  
% 2.23/1.07  
% 2.23/1.07  clauses                                 18
% 2.23/1.07  conjectures                             3
% 2.23/1.07  EPR                                     3
% 2.23/1.07  Horn                                    17
% 2.23/1.07  unary                                   7
% 2.23/1.07  binary                                  6
% 2.23/1.07  lits                                    34
% 2.23/1.07  lits eq                                 11
% 2.23/1.07  fd_pure                                 0
% 2.23/1.07  fd_pseudo                               0
% 2.23/1.07  fd_cond                                 0
% 2.23/1.07  fd_pseudo_cond                          2
% 2.23/1.07  AC symbols                              0
% 2.23/1.07  
% 2.23/1.07  ------ Schedule dynamic 5 is on 
% 2.23/1.07  
% 2.23/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.23/1.07  
% 2.23/1.07  
% 2.23/1.07  ------ 
% 2.23/1.07  Current options:
% 2.23/1.07  ------ 
% 2.23/1.07  
% 2.23/1.07  ------ Input Options
% 2.23/1.07  
% 2.23/1.07  --out_options                           all
% 2.23/1.07  --tptp_safe_out                         true
% 2.23/1.07  --problem_path                          ""
% 2.23/1.07  --include_path                          ""
% 2.23/1.07  --clausifier                            res/vclausify_rel
% 2.23/1.07  --clausifier_options                    --mode clausify
% 2.23/1.07  --stdin                                 false
% 2.23/1.07  --stats_out                             all
% 2.23/1.07  
% 2.23/1.07  ------ General Options
% 2.23/1.07  
% 2.23/1.07  --fof                                   false
% 2.23/1.07  --time_out_real                         305.
% 2.23/1.07  --time_out_virtual                      -1.
% 2.23/1.07  --symbol_type_check                     false
% 2.23/1.07  --clausify_out                          false
% 2.23/1.07  --sig_cnt_out                           false
% 2.23/1.07  --trig_cnt_out                          false
% 2.23/1.07  --trig_cnt_out_tolerance                1.
% 2.23/1.07  --trig_cnt_out_sk_spl                   false
% 2.23/1.07  --abstr_cl_out                          false
% 2.23/1.07  
% 2.23/1.07  ------ Global Options
% 2.23/1.07  
% 2.23/1.07  --schedule                              default
% 2.23/1.07  --add_important_lit                     false
% 2.23/1.07  --prop_solver_per_cl                    1000
% 2.23/1.07  --min_unsat_core                        false
% 2.23/1.07  --soft_assumptions                      false
% 2.23/1.07  --soft_lemma_size                       3
% 2.23/1.07  --prop_impl_unit_size                   0
% 2.23/1.07  --prop_impl_unit                        []
% 2.23/1.07  --share_sel_clauses                     true
% 2.23/1.07  --reset_solvers                         false
% 2.23/1.07  --bc_imp_inh                            [conj_cone]
% 2.23/1.07  --conj_cone_tolerance                   3.
% 2.23/1.07  --extra_neg_conj                        none
% 2.23/1.07  --large_theory_mode                     true
% 2.23/1.07  --prolific_symb_bound                   200
% 2.23/1.07  --lt_threshold                          2000
% 2.23/1.07  --clause_weak_htbl                      true
% 2.23/1.07  --gc_record_bc_elim                     false
% 2.23/1.07  
% 2.23/1.07  ------ Preprocessing Options
% 2.23/1.07  
% 2.23/1.07  --preprocessing_flag                    true
% 2.23/1.07  --time_out_prep_mult                    0.1
% 2.23/1.07  --splitting_mode                        input
% 2.23/1.07  --splitting_grd                         true
% 2.23/1.07  --splitting_cvd                         false
% 2.23/1.07  --splitting_cvd_svl                     false
% 2.23/1.07  --splitting_nvd                         32
% 2.23/1.07  --sub_typing                            true
% 2.23/1.07  --prep_gs_sim                           true
% 2.23/1.07  --prep_unflatten                        true
% 2.23/1.07  --prep_res_sim                          true
% 2.23/1.07  --prep_upred                            true
% 2.23/1.07  --prep_sem_filter                       exhaustive
% 2.23/1.07  --prep_sem_filter_out                   false
% 2.23/1.07  --pred_elim                             true
% 2.23/1.07  --res_sim_input                         true
% 2.23/1.07  --eq_ax_congr_red                       true
% 2.23/1.07  --pure_diseq_elim                       true
% 2.23/1.07  --brand_transform                       false
% 2.23/1.07  --non_eq_to_eq                          false
% 2.23/1.07  --prep_def_merge                        true
% 2.23/1.07  --prep_def_merge_prop_impl              false
% 2.23/1.07  --prep_def_merge_mbd                    true
% 2.23/1.07  --prep_def_merge_tr_red                 false
% 2.23/1.07  --prep_def_merge_tr_cl                  false
% 2.23/1.07  --smt_preprocessing                     true
% 2.23/1.07  --smt_ac_axioms                         fast
% 2.23/1.07  --preprocessed_out                      false
% 2.23/1.07  --preprocessed_stats                    false
% 2.23/1.07  
% 2.23/1.07  ------ Abstraction refinement Options
% 2.23/1.07  
% 2.23/1.07  --abstr_ref                             []
% 2.23/1.07  --abstr_ref_prep                        false
% 2.23/1.07  --abstr_ref_until_sat                   false
% 2.23/1.07  --abstr_ref_sig_restrict                funpre
% 2.23/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/1.07  --abstr_ref_under                       []
% 2.23/1.07  
% 2.23/1.07  ------ SAT Options
% 2.23/1.07  
% 2.23/1.07  --sat_mode                              false
% 2.23/1.07  --sat_fm_restart_options                ""
% 2.23/1.07  --sat_gr_def                            false
% 2.23/1.07  --sat_epr_types                         true
% 2.23/1.07  --sat_non_cyclic_types                  false
% 2.23/1.07  --sat_finite_models                     false
% 2.23/1.07  --sat_fm_lemmas                         false
% 2.23/1.07  --sat_fm_prep                           false
% 2.23/1.07  --sat_fm_uc_incr                        true
% 2.23/1.07  --sat_out_model                         small
% 2.23/1.07  --sat_out_clauses                       false
% 2.23/1.07  
% 2.23/1.07  ------ QBF Options
% 2.23/1.07  
% 2.23/1.07  --qbf_mode                              false
% 2.23/1.07  --qbf_elim_univ                         false
% 2.23/1.07  --qbf_dom_inst                          none
% 2.23/1.07  --qbf_dom_pre_inst                      false
% 2.23/1.07  --qbf_sk_in                             false
% 2.23/1.07  --qbf_pred_elim                         true
% 2.23/1.07  --qbf_split                             512
% 2.23/1.07  
% 2.23/1.07  ------ BMC1 Options
% 2.23/1.07  
% 2.23/1.07  --bmc1_incremental                      false
% 2.23/1.07  --bmc1_axioms                           reachable_all
% 2.23/1.07  --bmc1_min_bound                        0
% 2.23/1.07  --bmc1_max_bound                        -1
% 2.23/1.07  --bmc1_max_bound_default                -1
% 2.23/1.07  --bmc1_symbol_reachability              true
% 2.23/1.07  --bmc1_property_lemmas                  false
% 2.23/1.07  --bmc1_k_induction                      false
% 2.23/1.07  --bmc1_non_equiv_states                 false
% 2.23/1.07  --bmc1_deadlock                         false
% 2.23/1.07  --bmc1_ucm                              false
% 2.23/1.07  --bmc1_add_unsat_core                   none
% 2.23/1.07  --bmc1_unsat_core_children              false
% 2.23/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/1.07  --bmc1_out_stat                         full
% 2.23/1.07  --bmc1_ground_init                      false
% 2.23/1.07  --bmc1_pre_inst_next_state              false
% 2.23/1.07  --bmc1_pre_inst_state                   false
% 2.23/1.07  --bmc1_pre_inst_reach_state             false
% 2.23/1.07  --bmc1_out_unsat_core                   false
% 2.23/1.07  --bmc1_aig_witness_out                  false
% 2.23/1.07  --bmc1_verbose                          false
% 2.23/1.07  --bmc1_dump_clauses_tptp                false
% 2.23/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.23/1.07  --bmc1_dump_file                        -
% 2.23/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.23/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.23/1.07  --bmc1_ucm_extend_mode                  1
% 2.23/1.07  --bmc1_ucm_init_mode                    2
% 2.23/1.07  --bmc1_ucm_cone_mode                    none
% 2.23/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.23/1.07  --bmc1_ucm_relax_model                  4
% 2.23/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.23/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/1.07  --bmc1_ucm_layered_model                none
% 2.23/1.07  --bmc1_ucm_max_lemma_size               10
% 2.23/1.07  
% 2.23/1.07  ------ AIG Options
% 2.23/1.07  
% 2.23/1.07  --aig_mode                              false
% 2.23/1.07  
% 2.23/1.07  ------ Instantiation Options
% 2.23/1.07  
% 2.23/1.07  --instantiation_flag                    true
% 2.23/1.07  --inst_sos_flag                         false
% 2.23/1.07  --inst_sos_phase                        true
% 2.23/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/1.07  --inst_lit_sel_side                     none
% 2.23/1.07  --inst_solver_per_active                1400
% 2.23/1.07  --inst_solver_calls_frac                1.
% 2.23/1.07  --inst_passive_queue_type               priority_queues
% 2.23/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/1.07  --inst_passive_queues_freq              [25;2]
% 2.23/1.07  --inst_dismatching                      true
% 2.23/1.07  --inst_eager_unprocessed_to_passive     true
% 2.23/1.07  --inst_prop_sim_given                   true
% 2.23/1.07  --inst_prop_sim_new                     false
% 2.23/1.07  --inst_subs_new                         false
% 2.23/1.07  --inst_eq_res_simp                      false
% 2.23/1.07  --inst_subs_given                       false
% 2.23/1.07  --inst_orphan_elimination               true
% 2.23/1.07  --inst_learning_loop_flag               true
% 2.23/1.07  --inst_learning_start                   3000
% 2.23/1.07  --inst_learning_factor                  2
% 2.23/1.07  --inst_start_prop_sim_after_learn       3
% 2.23/1.07  --inst_sel_renew                        solver
% 2.23/1.07  --inst_lit_activity_flag                true
% 2.23/1.07  --inst_restr_to_given                   false
% 2.23/1.07  --inst_activity_threshold               500
% 2.23/1.07  --inst_out_proof                        true
% 2.23/1.07  
% 2.23/1.07  ------ Resolution Options
% 2.23/1.07  
% 2.23/1.07  --resolution_flag                       false
% 2.23/1.07  --res_lit_sel                           adaptive
% 2.23/1.07  --res_lit_sel_side                      none
% 2.23/1.07  --res_ordering                          kbo
% 2.23/1.07  --res_to_prop_solver                    active
% 2.23/1.07  --res_prop_simpl_new                    false
% 2.23/1.07  --res_prop_simpl_given                  true
% 2.23/1.07  --res_passive_queue_type                priority_queues
% 2.23/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/1.07  --res_passive_queues_freq               [15;5]
% 2.23/1.07  --res_forward_subs                      full
% 2.23/1.07  --res_backward_subs                     full
% 2.23/1.07  --res_forward_subs_resolution           true
% 2.23/1.07  --res_backward_subs_resolution          true
% 2.23/1.07  --res_orphan_elimination                true
% 2.23/1.07  --res_time_limit                        2.
% 2.23/1.07  --res_out_proof                         true
% 2.23/1.07  
% 2.23/1.07  ------ Superposition Options
% 2.23/1.07  
% 2.23/1.07  --superposition_flag                    true
% 2.23/1.07  --sup_passive_queue_type                priority_queues
% 2.23/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.23/1.07  --demod_completeness_check              fast
% 2.23/1.07  --demod_use_ground                      true
% 2.23/1.07  --sup_to_prop_solver                    passive
% 2.23/1.07  --sup_prop_simpl_new                    true
% 2.23/1.07  --sup_prop_simpl_given                  true
% 2.23/1.07  --sup_fun_splitting                     false
% 2.23/1.07  --sup_smt_interval                      50000
% 2.23/1.07  
% 2.23/1.07  ------ Superposition Simplification Setup
% 2.23/1.07  
% 2.23/1.07  --sup_indices_passive                   []
% 2.23/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.07  --sup_full_bw                           [BwDemod]
% 2.23/1.07  --sup_immed_triv                        [TrivRules]
% 2.23/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.07  --sup_immed_bw_main                     []
% 2.23/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.07  
% 2.23/1.07  ------ Combination Options
% 2.23/1.07  
% 2.23/1.07  --comb_res_mult                         3
% 2.23/1.07  --comb_sup_mult                         2
% 2.23/1.07  --comb_inst_mult                        10
% 2.23/1.07  
% 2.23/1.07  ------ Debug Options
% 2.23/1.07  
% 2.23/1.07  --dbg_backtrace                         false
% 2.23/1.07  --dbg_dump_prop_clauses                 false
% 2.23/1.07  --dbg_dump_prop_clauses_file            -
% 2.23/1.07  --dbg_out_stat                          false
% 2.23/1.07  
% 2.23/1.07  
% 2.23/1.07  
% 2.23/1.07  
% 2.23/1.07  ------ Proving...
% 2.23/1.07  
% 2.23/1.07  
% 2.23/1.07  % SZS status Theorem for theBenchmark.p
% 2.23/1.07  
% 2.23/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 2.23/1.07  
% 2.23/1.07  fof(f15,conjecture,(
% 2.23/1.07    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f16,negated_conjecture,(
% 2.23/1.07    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.23/1.07    inference(negated_conjecture,[],[f15])).
% 2.23/1.07  
% 2.23/1.07  fof(f17,plain,(
% 2.23/1.07    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.23/1.07    inference(pure_predicate_removal,[],[f16])).
% 2.23/1.07  
% 2.23/1.07  fof(f28,plain,(
% 2.23/1.07    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.23/1.07    inference(ennf_transformation,[],[f17])).
% 2.23/1.07  
% 2.23/1.07  fof(f29,plain,(
% 2.23/1.07    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.23/1.07    inference(flattening,[],[f28])).
% 2.23/1.07  
% 2.23/1.07  fof(f37,plain,(
% 2.23/1.07    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.23/1.07    introduced(choice_axiom,[])).
% 2.23/1.07  
% 2.23/1.07  fof(f38,plain,(
% 2.23/1.07    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.23/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f37])).
% 2.23/1.07  
% 2.23/1.07  fof(f60,plain,(
% 2.23/1.07    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.23/1.07    inference(cnf_transformation,[],[f38])).
% 2.23/1.07  
% 2.23/1.07  fof(f2,axiom,(
% 2.23/1.07    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f42,plain,(
% 2.23/1.07    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.23/1.07    inference(cnf_transformation,[],[f2])).
% 2.23/1.07  
% 2.23/1.07  fof(f3,axiom,(
% 2.23/1.07    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f43,plain,(
% 2.23/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.23/1.07    inference(cnf_transformation,[],[f3])).
% 2.23/1.07  
% 2.23/1.07  fof(f63,plain,(
% 2.23/1.07    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.23/1.07    inference(definition_unfolding,[],[f42,f43])).
% 2.23/1.07  
% 2.23/1.07  fof(f69,plain,(
% 2.23/1.07    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 2.23/1.07    inference(definition_unfolding,[],[f60,f63])).
% 2.23/1.07  
% 2.23/1.07  fof(f13,axiom,(
% 2.23/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f18,plain,(
% 2.23/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.23/1.07    inference(pure_predicate_removal,[],[f13])).
% 2.23/1.07  
% 2.23/1.07  fof(f26,plain,(
% 2.23/1.07    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/1.07    inference(ennf_transformation,[],[f18])).
% 2.23/1.07  
% 2.23/1.07  fof(f57,plain,(
% 2.23/1.07    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/1.07    inference(cnf_transformation,[],[f26])).
% 2.23/1.07  
% 2.23/1.07  fof(f8,axiom,(
% 2.23/1.07    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f20,plain,(
% 2.23/1.07    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/1.07    inference(ennf_transformation,[],[f8])).
% 2.23/1.07  
% 2.23/1.07  fof(f35,plain,(
% 2.23/1.07    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.23/1.07    inference(nnf_transformation,[],[f20])).
% 2.23/1.07  
% 2.23/1.07  fof(f50,plain,(
% 2.23/1.07    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.23/1.07    inference(cnf_transformation,[],[f35])).
% 2.23/1.07  
% 2.23/1.07  fof(f12,axiom,(
% 2.23/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f25,plain,(
% 2.23/1.07    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/1.07    inference(ennf_transformation,[],[f12])).
% 2.23/1.07  
% 2.23/1.07  fof(f56,plain,(
% 2.23/1.07    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/1.07    inference(cnf_transformation,[],[f25])).
% 2.23/1.07  
% 2.23/1.07  fof(f4,axiom,(
% 2.23/1.07    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f32,plain,(
% 2.23/1.07    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.23/1.07    inference(nnf_transformation,[],[f4])).
% 2.23/1.07  
% 2.23/1.07  fof(f33,plain,(
% 2.23/1.07    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.23/1.07    inference(flattening,[],[f32])).
% 2.23/1.07  
% 2.23/1.07  fof(f44,plain,(
% 2.23/1.07    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.23/1.07    inference(cnf_transformation,[],[f33])).
% 2.23/1.07  
% 2.23/1.07  fof(f66,plain,(
% 2.23/1.07    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 2.23/1.07    inference(definition_unfolding,[],[f44,f63,f63])).
% 2.23/1.07  
% 2.23/1.07  fof(f62,plain,(
% 2.23/1.07    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.23/1.07    inference(cnf_transformation,[],[f38])).
% 2.23/1.07  
% 2.23/1.07  fof(f68,plain,(
% 2.23/1.07    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.23/1.07    inference(definition_unfolding,[],[f62,f63,f63])).
% 2.23/1.07  
% 2.23/1.07  fof(f11,axiom,(
% 2.23/1.07    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f23,plain,(
% 2.23/1.07    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.23/1.07    inference(ennf_transformation,[],[f11])).
% 2.23/1.07  
% 2.23/1.07  fof(f24,plain,(
% 2.23/1.07    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.23/1.07    inference(flattening,[],[f23])).
% 2.23/1.07  
% 2.23/1.07  fof(f55,plain,(
% 2.23/1.07    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.23/1.07    inference(cnf_transformation,[],[f24])).
% 2.23/1.07  
% 2.23/1.07  fof(f67,plain,(
% 2.23/1.07    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_enumset1(X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.23/1.07    inference(definition_unfolding,[],[f55,f63,f63])).
% 2.23/1.07  
% 2.23/1.07  fof(f59,plain,(
% 2.23/1.07    v1_funct_1(sK3)),
% 2.23/1.07    inference(cnf_transformation,[],[f38])).
% 2.23/1.07  
% 2.23/1.07  fof(f14,axiom,(
% 2.23/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f27,plain,(
% 2.23/1.07    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/1.07    inference(ennf_transformation,[],[f14])).
% 2.23/1.07  
% 2.23/1.07  fof(f58,plain,(
% 2.23/1.07    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/1.07    inference(cnf_transformation,[],[f27])).
% 2.23/1.07  
% 2.23/1.07  fof(f9,axiom,(
% 2.23/1.07    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f21,plain,(
% 2.23/1.07    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.23/1.07    inference(ennf_transformation,[],[f9])).
% 2.23/1.07  
% 2.23/1.07  fof(f52,plain,(
% 2.23/1.07    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.23/1.07    inference(cnf_transformation,[],[f21])).
% 2.23/1.07  
% 2.23/1.07  fof(f10,axiom,(
% 2.23/1.07    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f22,plain,(
% 2.23/1.07    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.23/1.07    inference(ennf_transformation,[],[f10])).
% 2.23/1.07  
% 2.23/1.07  fof(f36,plain,(
% 2.23/1.07    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.23/1.07    inference(nnf_transformation,[],[f22])).
% 2.23/1.07  
% 2.23/1.07  fof(f53,plain,(
% 2.23/1.07    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/1.07    inference(cnf_transformation,[],[f36])).
% 2.23/1.07  
% 2.23/1.07  fof(f5,axiom,(
% 2.23/1.07    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f47,plain,(
% 2.23/1.07    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.23/1.07    inference(cnf_transformation,[],[f5])).
% 2.23/1.07  
% 2.23/1.07  fof(f6,axiom,(
% 2.23/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f34,plain,(
% 2.23/1.07    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.23/1.07    inference(nnf_transformation,[],[f6])).
% 2.23/1.07  
% 2.23/1.07  fof(f48,plain,(
% 2.23/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.23/1.07    inference(cnf_transformation,[],[f34])).
% 2.23/1.07  
% 2.23/1.07  fof(f1,axiom,(
% 2.23/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.23/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.07  
% 2.23/1.07  fof(f30,plain,(
% 2.23/1.07    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.23/1.07    inference(nnf_transformation,[],[f1])).
% 2.23/1.07  
% 2.23/1.07  fof(f31,plain,(
% 2.23/1.07    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.23/1.07    inference(flattening,[],[f30])).
% 2.23/1.07  
% 2.23/1.07  fof(f41,plain,(
% 2.23/1.07    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.23/1.07    inference(cnf_transformation,[],[f31])).
% 2.23/1.07  
% 2.23/1.07  fof(f45,plain,(
% 2.23/1.07    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 2.23/1.07    inference(cnf_transformation,[],[f33])).
% 2.23/1.07  
% 2.23/1.07  fof(f65,plain,(
% 2.23/1.07    ( ! [X0,X1] : (r1_tarski(X0,k1_enumset1(X1,X1,X1)) | k1_xboole_0 != X0) )),
% 2.23/1.07    inference(definition_unfolding,[],[f45,f63])).
% 2.23/1.07  
% 2.23/1.07  fof(f73,plain,(
% 2.23/1.07    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X1))) )),
% 2.23/1.07    inference(equality_resolution,[],[f65])).
% 2.23/1.07  
% 2.23/1.07  cnf(c_20,negated_conjecture,
% 2.23/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
% 2.23/1.07      inference(cnf_transformation,[],[f69]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1325,plain,
% 2.23/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_16,plain,
% 2.23/1.07      ( v4_relat_1(X0,X1)
% 2.23/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.23/1.07      inference(cnf_transformation,[],[f57]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_10,plain,
% 2.23/1.07      ( ~ v4_relat_1(X0,X1)
% 2.23/1.07      | r1_tarski(k1_relat_1(X0),X1)
% 2.23/1.07      | ~ v1_relat_1(X0) ),
% 2.23/1.07      inference(cnf_transformation,[],[f50]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_295,plain,
% 2.23/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.07      | r1_tarski(k1_relat_1(X0),X1)
% 2.23/1.07      | ~ v1_relat_1(X0) ),
% 2.23/1.07      inference(resolution,[status(thm)],[c_16,c_10]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_15,plain,
% 2.23/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.07      | v1_relat_1(X0) ),
% 2.23/1.07      inference(cnf_transformation,[],[f56]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_299,plain,
% 2.23/1.07      ( r1_tarski(k1_relat_1(X0),X1)
% 2.23/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.23/1.07      inference(global_propositional_subsumption,
% 2.23/1.07                [status(thm)],
% 2.23/1.07                [c_295,c_15]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_300,plain,
% 2.23/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.07      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.23/1.07      inference(renaming,[status(thm)],[c_299]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1323,plain,
% 2.23/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.23/1.07      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1706,plain,
% 2.23/1.07      ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
% 2.23/1.07      inference(superposition,[status(thm)],[c_1325,c_1323]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_5,plain,
% 2.23/1.07      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
% 2.23/1.07      | k1_enumset1(X1,X1,X1) = X0
% 2.23/1.07      | k1_xboole_0 = X0 ),
% 2.23/1.07      inference(cnf_transformation,[],[f66]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1335,plain,
% 2.23/1.07      ( k1_enumset1(X0,X0,X0) = X1
% 2.23/1.07      | k1_xboole_0 = X1
% 2.23/1.07      | r1_tarski(X1,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_2657,plain,
% 2.23/1.07      ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.23/1.07      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.23/1.07      inference(superposition,[status(thm)],[c_1706,c_1335]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_23,plain,
% 2.23/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_18,negated_conjecture,
% 2.23/1.07      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.23/1.07      inference(cnf_transformation,[],[f68]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_14,plain,
% 2.23/1.07      ( ~ v1_funct_1(X0)
% 2.23/1.07      | ~ v1_relat_1(X0)
% 2.23/1.07      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 2.23/1.07      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.23/1.07      inference(cnf_transformation,[],[f67]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_21,negated_conjecture,
% 2.23/1.07      ( v1_funct_1(sK3) ),
% 2.23/1.07      inference(cnf_transformation,[],[f59]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_276,plain,
% 2.23/1.07      ( ~ v1_relat_1(X0)
% 2.23/1.07      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 2.23/1.07      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.23/1.07      | sK3 != X0 ),
% 2.23/1.07      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_277,plain,
% 2.23/1.07      ( ~ v1_relat_1(sK3)
% 2.23/1.07      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 2.23/1.07      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.23/1.07      inference(unflattening,[status(thm)],[c_276]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_278,plain,
% 2.23/1.07      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 2.23/1.07      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.23/1.07      | v1_relat_1(sK3) != iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_280,plain,
% 2.23/1.07      ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.23/1.07      | k1_enumset1(sK0,sK0,sK0) != k1_relat_1(sK3)
% 2.23/1.07      | v1_relat_1(sK3) != iProver_top ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_278]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1463,plain,
% 2.23/1.07      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 2.23/1.07      | v1_relat_1(sK3) ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_15]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1464,plain,
% 2.23/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
% 2.23/1.07      | v1_relat_1(sK3) = iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_17,plain,
% 2.23/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.07      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.23/1.07      inference(cnf_transformation,[],[f58]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1504,plain,
% 2.23/1.07      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 2.23/1.07      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_17]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1590,plain,
% 2.23/1.07      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 2.23/1.07      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_1504]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_899,plain,
% 2.23/1.07      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.23/1.07      theory(equality) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1485,plain,
% 2.23/1.07      ( ~ r1_tarski(X0,X1)
% 2.23/1.07      | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.23/1.07      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 2.23/1.07      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_899]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1589,plain,
% 2.23/1.07      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.23/1.07      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.23/1.07      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.23/1.07      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_1485]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1680,plain,
% 2.23/1.07      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.23/1.07      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.23/1.07      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.23/1.07      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_1589]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_11,plain,
% 2.23/1.07      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.23/1.07      inference(cnf_transformation,[],[f52]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1537,plain,
% 2.23/1.07      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
% 2.23/1.07      | ~ v1_relat_1(sK3) ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_11]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1681,plain,
% 2.23/1.07      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.23/1.07      | ~ v1_relat_1(sK3) ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_1537]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_2959,plain,
% 2.23/1.07      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.23/1.07      inference(global_propositional_subsumption,
% 2.23/1.07                [status(thm)],
% 2.23/1.07                [c_2657,c_20,c_23,c_18,c_280,c_1463,c_1464,c_1590,c_1680,
% 2.23/1.07                 c_1681]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_13,plain,
% 2.23/1.07      ( ~ v1_relat_1(X0)
% 2.23/1.07      | k2_relat_1(X0) = k1_xboole_0
% 2.23/1.07      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.23/1.07      inference(cnf_transformation,[],[f53]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1329,plain,
% 2.23/1.07      ( k2_relat_1(X0) = k1_xboole_0
% 2.23/1.07      | k1_relat_1(X0) != k1_xboole_0
% 2.23/1.07      | v1_relat_1(X0) != iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_2974,plain,
% 2.23/1.07      ( k2_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.23/1.07      inference(superposition,[status(thm)],[c_2959,c_1329]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1538,plain,
% 2.23/1.07      ( ~ v1_relat_1(sK3)
% 2.23/1.07      | k2_relat_1(sK3) = k1_xboole_0
% 2.23/1.07      | k1_relat_1(sK3) != k1_xboole_0 ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_13]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_3114,plain,
% 2.23/1.07      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.23/1.07      inference(global_propositional_subsumption,
% 2.23/1.07                [status(thm)],
% 2.23/1.07                [c_2974,c_20,c_23,c_18,c_280,c_1463,c_1464,c_1538,c_1590,
% 2.23/1.07                 c_1680,c_1681,c_2657]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1331,plain,
% 2.23/1.07      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 2.23/1.07      | v1_relat_1(X0) != iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_3120,plain,
% 2.23/1.07      ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top
% 2.23/1.07      | v1_relat_1(sK3) != iProver_top ),
% 2.23/1.07      inference(superposition,[status(thm)],[c_3114,c_1331]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_3517,plain,
% 2.23/1.07      ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top ),
% 2.23/1.07      inference(global_propositional_subsumption,
% 2.23/1.07                [status(thm)],
% 2.23/1.07                [c_3120,c_23,c_1464]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_6,plain,
% 2.23/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.23/1.07      inference(cnf_transformation,[],[f47]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1334,plain,
% 2.23/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_8,plain,
% 2.23/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.23/1.07      inference(cnf_transformation,[],[f48]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1332,plain,
% 2.23/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.23/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1620,plain,
% 2.23/1.07      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.23/1.07      inference(superposition,[status(thm)],[c_1334,c_1332]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_0,plain,
% 2.23/1.07      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.23/1.07      inference(cnf_transformation,[],[f41]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1339,plain,
% 2.23/1.07      ( X0 = X1
% 2.23/1.07      | r1_tarski(X0,X1) != iProver_top
% 2.23/1.07      | r1_tarski(X1,X0) != iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_2415,plain,
% 2.23/1.07      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.23/1.07      inference(superposition,[status(thm)],[c_1620,c_1339]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_3525,plain,
% 2.23/1.07      ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
% 2.23/1.07      inference(superposition,[status(thm)],[c_3517,c_2415]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1327,plain,
% 2.23/1.07      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.23/1.07      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_2464,plain,
% 2.23/1.07      ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.23/1.07      inference(superposition,[status(thm)],[c_1325,c_1327]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_1326,plain,
% 2.23/1.07      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_2773,plain,
% 2.23/1.07      ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.23/1.07      inference(demodulation,[status(thm)],[c_2464,c_1326]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_3535,plain,
% 2.23/1.07      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.23/1.07      inference(demodulation,[status(thm)],[c_3525,c_2773]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_4,plain,
% 2.23/1.07      ( r1_tarski(k1_xboole_0,k1_enumset1(X0,X0,X0)) ),
% 2.23/1.07      inference(cnf_transformation,[],[f73]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_2171,plain,
% 2.23/1.07      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.23/1.07      inference(instantiation,[status(thm)],[c_4]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(c_2174,plain,
% 2.23/1.07      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
% 2.23/1.07      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 2.23/1.07  
% 2.23/1.07  cnf(contradiction,plain,
% 2.23/1.07      ( $false ),
% 2.23/1.07      inference(minisat,[status(thm)],[c_3535,c_2174]) ).
% 2.23/1.07  
% 2.23/1.07  
% 2.23/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.23/1.07  
% 2.23/1.07  ------                               Statistics
% 2.23/1.07  
% 2.23/1.07  ------ General
% 2.23/1.07  
% 2.23/1.07  abstr_ref_over_cycles:                  0
% 2.23/1.07  abstr_ref_under_cycles:                 0
% 2.23/1.07  gc_basic_clause_elim:                   0
% 2.23/1.07  forced_gc_time:                         0
% 2.23/1.07  parsing_time:                           0.011
% 2.23/1.07  unif_index_cands_time:                  0.
% 2.23/1.07  unif_index_add_time:                    0.
% 2.23/1.07  orderings_time:                         0.
% 2.23/1.07  out_proof_time:                         0.029
% 2.23/1.07  total_time:                             0.257
% 2.23/1.07  num_of_symbols:                         49
% 2.23/1.07  num_of_terms:                           2759
% 2.23/1.07  
% 2.23/1.07  ------ Preprocessing
% 2.23/1.07  
% 2.23/1.07  num_of_splits:                          0
% 2.23/1.07  num_of_split_atoms:                     0
% 2.23/1.07  num_of_reused_defs:                     0
% 2.23/1.07  num_eq_ax_congr_red:                    11
% 2.23/1.07  num_of_sem_filtered_clauses:            1
% 2.23/1.07  num_of_subtypes:                        0
% 2.23/1.07  monotx_restored_types:                  0
% 2.23/1.07  sat_num_of_epr_types:                   0
% 2.23/1.07  sat_num_of_non_cyclic_types:            0
% 2.23/1.07  sat_guarded_non_collapsed_types:        0
% 2.23/1.07  num_pure_diseq_elim:                    0
% 2.23/1.07  simp_replaced_by:                       0
% 2.23/1.07  res_preprocessed:                       100
% 2.23/1.07  prep_upred:                             0
% 2.23/1.07  prep_unflattend:                        25
% 2.23/1.07  smt_new_axioms:                         0
% 2.23/1.07  pred_elim_cands:                        3
% 2.23/1.07  pred_elim:                              2
% 2.23/1.07  pred_elim_cl:                           3
% 2.23/1.07  pred_elim_cycles:                       6
% 2.23/1.07  merged_defs:                            8
% 2.23/1.07  merged_defs_ncl:                        0
% 2.23/1.07  bin_hyper_res:                          8
% 2.23/1.07  prep_cycles:                            4
% 2.23/1.07  pred_elim_time:                         0.011
% 2.23/1.07  splitting_time:                         0.
% 2.23/1.07  sem_filter_time:                        0.
% 2.23/1.07  monotx_time:                            0.
% 2.23/1.07  subtype_inf_time:                       0.
% 2.23/1.07  
% 2.23/1.07  ------ Problem properties
% 2.23/1.07  
% 2.23/1.07  clauses:                                18
% 2.23/1.07  conjectures:                            3
% 2.23/1.07  epr:                                    3
% 2.23/1.07  horn:                                   17
% 2.23/1.07  ground:                                 3
% 2.23/1.07  unary:                                  7
% 2.23/1.07  binary:                                 6
% 2.23/1.07  lits:                                   34
% 2.23/1.07  lits_eq:                                11
% 2.23/1.07  fd_pure:                                0
% 2.23/1.07  fd_pseudo:                              0
% 2.23/1.07  fd_cond:                                0
% 2.23/1.07  fd_pseudo_cond:                         2
% 2.23/1.07  ac_symbols:                             0
% 2.23/1.07  
% 2.23/1.07  ------ Propositional Solver
% 2.23/1.07  
% 2.23/1.07  prop_solver_calls:                      27
% 2.23/1.07  prop_fast_solver_calls:                 590
% 2.23/1.07  smt_solver_calls:                       0
% 2.23/1.07  smt_fast_solver_calls:                  0
% 2.23/1.07  prop_num_of_clauses:                    1267
% 2.23/1.07  prop_preprocess_simplified:             4276
% 2.23/1.07  prop_fo_subsumed:                       6
% 2.23/1.07  prop_solver_time:                       0.
% 2.23/1.07  smt_solver_time:                        0.
% 2.23/1.07  smt_fast_solver_time:                   0.
% 2.23/1.07  prop_fast_solver_time:                  0.
% 2.23/1.07  prop_unsat_core_time:                   0.
% 2.23/1.07  
% 2.23/1.07  ------ QBF
% 2.23/1.07  
% 2.23/1.07  qbf_q_res:                              0
% 2.23/1.07  qbf_num_tautologies:                    0
% 2.23/1.07  qbf_prep_cycles:                        0
% 2.23/1.07  
% 2.23/1.07  ------ BMC1
% 2.23/1.07  
% 2.23/1.07  bmc1_current_bound:                     -1
% 2.23/1.07  bmc1_last_solved_bound:                 -1
% 2.23/1.07  bmc1_unsat_core_size:                   -1
% 2.23/1.07  bmc1_unsat_core_parents_size:           -1
% 2.23/1.07  bmc1_merge_next_fun:                    0
% 2.23/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.23/1.07  
% 2.23/1.07  ------ Instantiation
% 2.23/1.07  
% 2.23/1.07  inst_num_of_clauses:                    371
% 2.23/1.07  inst_num_in_passive:                    60
% 2.23/1.07  inst_num_in_active:                     203
% 2.23/1.07  inst_num_in_unprocessed:                109
% 2.23/1.07  inst_num_of_loops:                      210
% 2.23/1.07  inst_num_of_learning_restarts:          0
% 2.23/1.07  inst_num_moves_active_passive:          5
% 2.23/1.07  inst_lit_activity:                      0
% 2.23/1.07  inst_lit_activity_moves:                0
% 2.23/1.07  inst_num_tautologies:                   0
% 2.23/1.07  inst_num_prop_implied:                  0
% 2.23/1.07  inst_num_existing_simplified:           0
% 2.23/1.07  inst_num_eq_res_simplified:             0
% 2.23/1.07  inst_num_child_elim:                    0
% 2.23/1.07  inst_num_of_dismatching_blockings:      83
% 2.23/1.07  inst_num_of_non_proper_insts:           434
% 2.23/1.07  inst_num_of_duplicates:                 0
% 2.23/1.07  inst_inst_num_from_inst_to_res:         0
% 2.23/1.07  inst_dismatching_checking_time:         0.
% 2.23/1.07  
% 2.23/1.07  ------ Resolution
% 2.23/1.07  
% 2.23/1.07  res_num_of_clauses:                     0
% 2.23/1.07  res_num_in_passive:                     0
% 2.23/1.07  res_num_in_active:                      0
% 2.23/1.07  res_num_of_loops:                       104
% 2.23/1.07  res_forward_subset_subsumed:            52
% 2.23/1.07  res_backward_subset_subsumed:           2
% 2.23/1.07  res_forward_subsumed:                   0
% 2.23/1.07  res_backward_subsumed:                  0
% 2.23/1.07  res_forward_subsumption_resolution:     0
% 2.23/1.07  res_backward_subsumption_resolution:    0
% 2.23/1.07  res_clause_to_clause_subsumption:       169
% 2.23/1.07  res_orphan_elimination:                 0
% 2.23/1.07  res_tautology_del:                      42
% 2.23/1.07  res_num_eq_res_simplified:              0
% 2.23/1.07  res_num_sel_changes:                    0
% 2.23/1.07  res_moves_from_active_to_pass:          0
% 2.23/1.07  
% 2.23/1.07  ------ Superposition
% 2.23/1.07  
% 2.23/1.07  sup_time_total:                         0.
% 2.23/1.07  sup_time_generating:                    0.
% 2.23/1.07  sup_time_sim_full:                      0.
% 2.23/1.07  sup_time_sim_immed:                     0.
% 2.23/1.07  
% 2.23/1.07  sup_num_of_clauses:                     48
% 2.23/1.07  sup_num_in_active:                      33
% 2.23/1.07  sup_num_in_passive:                     15
% 2.23/1.07  sup_num_of_loops:                       41
% 2.23/1.07  sup_fw_superposition:                   38
% 2.23/1.07  sup_bw_superposition:                   11
% 2.23/1.07  sup_immediate_simplified:               4
% 2.23/1.07  sup_given_eliminated:                   1
% 2.23/1.07  comparisons_done:                       0
% 2.23/1.07  comparisons_avoided:                    0
% 2.23/1.07  
% 2.23/1.07  ------ Simplifications
% 2.23/1.07  
% 2.23/1.07  
% 2.23/1.07  sim_fw_subset_subsumed:                 2
% 2.23/1.07  sim_bw_subset_subsumed:                 0
% 2.23/1.07  sim_fw_subsumed:                        3
% 2.23/1.07  sim_bw_subsumed:                        0
% 2.23/1.07  sim_fw_subsumption_res:                 0
% 2.23/1.07  sim_bw_subsumption_res:                 0
% 2.23/1.07  sim_tautology_del:                      1
% 2.23/1.07  sim_eq_tautology_del:                   6
% 2.23/1.07  sim_eq_res_simp:                        0
% 2.23/1.07  sim_fw_demodulated:                     0
% 2.23/1.07  sim_bw_demodulated:                     8
% 2.23/1.07  sim_light_normalised:                   0
% 2.23/1.07  sim_joinable_taut:                      0
% 2.23/1.07  sim_joinable_simp:                      0
% 2.23/1.07  sim_ac_normalised:                      0
% 2.23/1.07  sim_smt_subsumption:                    0
% 2.23/1.07  
%------------------------------------------------------------------------------
