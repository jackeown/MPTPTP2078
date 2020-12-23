%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:33 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 558 expanded)
%              Number of clauses        :   70 ( 147 expanded)
%              Number of leaves         :   19 ( 130 expanded)
%              Depth                    :   19
%              Number of atoms          :  310 (1385 expanded)
%              Number of equality atoms :  155 ( 570 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f37])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f45,f64,f64])).

fof(f63,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f63,f64,f64])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f64,f64])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1023,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1447,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1023])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1135,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1137,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1135])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1136,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1139,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_1543,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1447,c_1137,c_1139])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1028,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1030,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1744,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1030])).

cnf(c_2038,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1543,c_1744])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1017,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_9])).

cnf(c_327,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_16])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_1015,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1325,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1017,c_1015])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1025,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1917,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1325,c_1025])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1018,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2131,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1018])).

cnf(c_1143,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1181,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1225,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1181])).

cnf(c_1380,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_722,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1164,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_1224,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1381,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_226,plain,
    ( ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_227,plain,
    ( ~ v1_relat_1(sK3)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_1016,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_228,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_1144,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_1157,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1016,c_24,c_228,c_1144])).

cnf(c_1158,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1157])).

cnf(c_2128,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1917,c_1158])).

cnf(c_2315,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2131,c_21,c_19,c_1143,c_1225,c_1380,c_1381,c_2128])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1021,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2333,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_1021])).

cnf(c_1243,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_720,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1256,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_721,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1457,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_2070,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_2071,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2070])).

cnf(c_2404,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2333,c_21,c_19,c_1143,c_1225,c_1243,c_1256,c_1380,c_1381,c_2071,c_2128])).

cnf(c_1019,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1926,plain,
    ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1017,c_1019])).

cnf(c_2159,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1926,c_1018])).

cnf(c_2408,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2404,c_2159])).

cnf(c_2615,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2038,c_2408])).

cnf(c_2777,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2615,c_1028])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.22/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.22/1.03  
% 1.22/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.22/1.03  
% 1.22/1.03  ------  iProver source info
% 1.22/1.03  
% 1.22/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.22/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.22/1.03  git: non_committed_changes: false
% 1.22/1.03  git: last_make_outside_of_git: false
% 1.22/1.03  
% 1.22/1.03  ------ 
% 1.22/1.03  
% 1.22/1.03  ------ Input Options
% 1.22/1.03  
% 1.22/1.03  --out_options                           all
% 1.22/1.03  --tptp_safe_out                         true
% 1.22/1.03  --problem_path                          ""
% 1.22/1.03  --include_path                          ""
% 1.22/1.03  --clausifier                            res/vclausify_rel
% 1.22/1.03  --clausifier_options                    --mode clausify
% 1.22/1.03  --stdin                                 false
% 1.22/1.03  --stats_out                             all
% 1.22/1.03  
% 1.22/1.03  ------ General Options
% 1.22/1.03  
% 1.22/1.03  --fof                                   false
% 1.22/1.03  --time_out_real                         305.
% 1.22/1.03  --time_out_virtual                      -1.
% 1.22/1.03  --symbol_type_check                     false
% 1.22/1.03  --clausify_out                          false
% 1.22/1.03  --sig_cnt_out                           false
% 1.22/1.03  --trig_cnt_out                          false
% 1.22/1.03  --trig_cnt_out_tolerance                1.
% 1.22/1.03  --trig_cnt_out_sk_spl                   false
% 1.22/1.03  --abstr_cl_out                          false
% 1.22/1.03  
% 1.22/1.03  ------ Global Options
% 1.22/1.03  
% 1.22/1.03  --schedule                              default
% 1.22/1.03  --add_important_lit                     false
% 1.22/1.03  --prop_solver_per_cl                    1000
% 1.22/1.03  --min_unsat_core                        false
% 1.22/1.03  --soft_assumptions                      false
% 1.22/1.03  --soft_lemma_size                       3
% 1.22/1.03  --prop_impl_unit_size                   0
% 1.22/1.03  --prop_impl_unit                        []
% 1.22/1.03  --share_sel_clauses                     true
% 1.22/1.03  --reset_solvers                         false
% 1.22/1.03  --bc_imp_inh                            [conj_cone]
% 1.22/1.03  --conj_cone_tolerance                   3.
% 1.22/1.03  --extra_neg_conj                        none
% 1.22/1.03  --large_theory_mode                     true
% 1.22/1.03  --prolific_symb_bound                   200
% 1.22/1.03  --lt_threshold                          2000
% 1.22/1.03  --clause_weak_htbl                      true
% 1.22/1.03  --gc_record_bc_elim                     false
% 1.22/1.03  
% 1.22/1.03  ------ Preprocessing Options
% 1.22/1.03  
% 1.22/1.03  --preprocessing_flag                    true
% 1.22/1.03  --time_out_prep_mult                    0.1
% 1.22/1.03  --splitting_mode                        input
% 1.22/1.03  --splitting_grd                         true
% 1.22/1.03  --splitting_cvd                         false
% 1.22/1.03  --splitting_cvd_svl                     false
% 1.22/1.03  --splitting_nvd                         32
% 1.22/1.03  --sub_typing                            true
% 1.22/1.03  --prep_gs_sim                           true
% 1.22/1.03  --prep_unflatten                        true
% 1.22/1.03  --prep_res_sim                          true
% 1.22/1.03  --prep_upred                            true
% 1.22/1.03  --prep_sem_filter                       exhaustive
% 1.22/1.03  --prep_sem_filter_out                   false
% 1.22/1.03  --pred_elim                             true
% 1.22/1.03  --res_sim_input                         true
% 1.22/1.03  --eq_ax_congr_red                       true
% 1.22/1.03  --pure_diseq_elim                       true
% 1.22/1.03  --brand_transform                       false
% 1.22/1.03  --non_eq_to_eq                          false
% 1.22/1.03  --prep_def_merge                        true
% 1.22/1.03  --prep_def_merge_prop_impl              false
% 1.22/1.03  --prep_def_merge_mbd                    true
% 1.22/1.03  --prep_def_merge_tr_red                 false
% 1.22/1.03  --prep_def_merge_tr_cl                  false
% 1.22/1.03  --smt_preprocessing                     true
% 1.22/1.03  --smt_ac_axioms                         fast
% 1.22/1.03  --preprocessed_out                      false
% 1.22/1.03  --preprocessed_stats                    false
% 1.22/1.03  
% 1.22/1.03  ------ Abstraction refinement Options
% 1.22/1.03  
% 1.22/1.03  --abstr_ref                             []
% 1.22/1.03  --abstr_ref_prep                        false
% 1.22/1.03  --abstr_ref_until_sat                   false
% 1.22/1.03  --abstr_ref_sig_restrict                funpre
% 1.22/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.22/1.03  --abstr_ref_under                       []
% 1.22/1.03  
% 1.22/1.03  ------ SAT Options
% 1.22/1.03  
% 1.22/1.03  --sat_mode                              false
% 1.22/1.03  --sat_fm_restart_options                ""
% 1.22/1.03  --sat_gr_def                            false
% 1.22/1.03  --sat_epr_types                         true
% 1.22/1.03  --sat_non_cyclic_types                  false
% 1.22/1.03  --sat_finite_models                     false
% 1.22/1.03  --sat_fm_lemmas                         false
% 1.22/1.03  --sat_fm_prep                           false
% 1.22/1.03  --sat_fm_uc_incr                        true
% 1.22/1.03  --sat_out_model                         small
% 1.22/1.03  --sat_out_clauses                       false
% 1.22/1.03  
% 1.22/1.03  ------ QBF Options
% 1.22/1.03  
% 1.22/1.03  --qbf_mode                              false
% 1.22/1.03  --qbf_elim_univ                         false
% 1.22/1.03  --qbf_dom_inst                          none
% 1.22/1.03  --qbf_dom_pre_inst                      false
% 1.22/1.03  --qbf_sk_in                             false
% 1.22/1.03  --qbf_pred_elim                         true
% 1.22/1.03  --qbf_split                             512
% 1.22/1.03  
% 1.22/1.03  ------ BMC1 Options
% 1.22/1.03  
% 1.22/1.03  --bmc1_incremental                      false
% 1.22/1.03  --bmc1_axioms                           reachable_all
% 1.22/1.03  --bmc1_min_bound                        0
% 1.22/1.03  --bmc1_max_bound                        -1
% 1.22/1.03  --bmc1_max_bound_default                -1
% 1.22/1.03  --bmc1_symbol_reachability              true
% 1.22/1.03  --bmc1_property_lemmas                  false
% 1.22/1.03  --bmc1_k_induction                      false
% 1.22/1.03  --bmc1_non_equiv_states                 false
% 1.22/1.03  --bmc1_deadlock                         false
% 1.22/1.03  --bmc1_ucm                              false
% 1.22/1.03  --bmc1_add_unsat_core                   none
% 1.22/1.03  --bmc1_unsat_core_children              false
% 1.22/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.22/1.03  --bmc1_out_stat                         full
% 1.22/1.03  --bmc1_ground_init                      false
% 1.22/1.03  --bmc1_pre_inst_next_state              false
% 1.22/1.03  --bmc1_pre_inst_state                   false
% 1.22/1.03  --bmc1_pre_inst_reach_state             false
% 1.22/1.03  --bmc1_out_unsat_core                   false
% 1.22/1.03  --bmc1_aig_witness_out                  false
% 1.22/1.03  --bmc1_verbose                          false
% 1.22/1.03  --bmc1_dump_clauses_tptp                false
% 1.22/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.22/1.03  --bmc1_dump_file                        -
% 1.22/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.22/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.22/1.03  --bmc1_ucm_extend_mode                  1
% 1.22/1.03  --bmc1_ucm_init_mode                    2
% 1.22/1.03  --bmc1_ucm_cone_mode                    none
% 1.22/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.22/1.03  --bmc1_ucm_relax_model                  4
% 1.22/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.22/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.22/1.03  --bmc1_ucm_layered_model                none
% 1.22/1.03  --bmc1_ucm_max_lemma_size               10
% 1.22/1.03  
% 1.22/1.03  ------ AIG Options
% 1.22/1.03  
% 1.22/1.03  --aig_mode                              false
% 1.22/1.03  
% 1.22/1.03  ------ Instantiation Options
% 1.22/1.03  
% 1.22/1.03  --instantiation_flag                    true
% 1.22/1.03  --inst_sos_flag                         false
% 1.22/1.03  --inst_sos_phase                        true
% 1.22/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.22/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.22/1.03  --inst_lit_sel_side                     num_symb
% 1.22/1.03  --inst_solver_per_active                1400
% 1.22/1.03  --inst_solver_calls_frac                1.
% 1.22/1.03  --inst_passive_queue_type               priority_queues
% 1.22/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.22/1.03  --inst_passive_queues_freq              [25;2]
% 1.22/1.03  --inst_dismatching                      true
% 1.22/1.03  --inst_eager_unprocessed_to_passive     true
% 1.22/1.03  --inst_prop_sim_given                   true
% 1.22/1.03  --inst_prop_sim_new                     false
% 1.22/1.03  --inst_subs_new                         false
% 1.22/1.03  --inst_eq_res_simp                      false
% 1.22/1.03  --inst_subs_given                       false
% 1.22/1.03  --inst_orphan_elimination               true
% 1.22/1.03  --inst_learning_loop_flag               true
% 1.22/1.03  --inst_learning_start                   3000
% 1.22/1.03  --inst_learning_factor                  2
% 1.22/1.03  --inst_start_prop_sim_after_learn       3
% 1.22/1.03  --inst_sel_renew                        solver
% 1.22/1.03  --inst_lit_activity_flag                true
% 1.22/1.03  --inst_restr_to_given                   false
% 1.22/1.03  --inst_activity_threshold               500
% 1.22/1.03  --inst_out_proof                        true
% 1.22/1.03  
% 1.22/1.03  ------ Resolution Options
% 1.22/1.03  
% 1.22/1.03  --resolution_flag                       true
% 1.22/1.03  --res_lit_sel                           adaptive
% 1.22/1.03  --res_lit_sel_side                      none
% 1.22/1.03  --res_ordering                          kbo
% 1.22/1.03  --res_to_prop_solver                    active
% 1.22/1.03  --res_prop_simpl_new                    false
% 1.22/1.03  --res_prop_simpl_given                  true
% 1.22/1.03  --res_passive_queue_type                priority_queues
% 1.22/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.22/1.03  --res_passive_queues_freq               [15;5]
% 1.22/1.03  --res_forward_subs                      full
% 1.22/1.03  --res_backward_subs                     full
% 1.22/1.03  --res_forward_subs_resolution           true
% 1.22/1.03  --res_backward_subs_resolution          true
% 1.22/1.03  --res_orphan_elimination                true
% 1.22/1.03  --res_time_limit                        2.
% 1.22/1.03  --res_out_proof                         true
% 1.22/1.03  
% 1.22/1.03  ------ Superposition Options
% 1.22/1.03  
% 1.22/1.03  --superposition_flag                    true
% 1.22/1.03  --sup_passive_queue_type                priority_queues
% 1.22/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.22/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.22/1.03  --demod_completeness_check              fast
% 1.22/1.03  --demod_use_ground                      true
% 1.22/1.03  --sup_to_prop_solver                    passive
% 1.22/1.03  --sup_prop_simpl_new                    true
% 1.22/1.03  --sup_prop_simpl_given                  true
% 1.22/1.03  --sup_fun_splitting                     false
% 1.22/1.03  --sup_smt_interval                      50000
% 1.22/1.03  
% 1.22/1.03  ------ Superposition Simplification Setup
% 1.22/1.03  
% 1.22/1.03  --sup_indices_passive                   []
% 1.22/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.22/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_full_bw                           [BwDemod]
% 1.22/1.03  --sup_immed_triv                        [TrivRules]
% 1.22/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.22/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_immed_bw_main                     []
% 1.22/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.22/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.03  
% 1.22/1.03  ------ Combination Options
% 1.22/1.03  
% 1.22/1.03  --comb_res_mult                         3
% 1.22/1.03  --comb_sup_mult                         2
% 1.22/1.03  --comb_inst_mult                        10
% 1.22/1.03  
% 1.22/1.03  ------ Debug Options
% 1.22/1.03  
% 1.22/1.03  --dbg_backtrace                         false
% 1.22/1.03  --dbg_dump_prop_clauses                 false
% 1.22/1.03  --dbg_dump_prop_clauses_file            -
% 1.22/1.03  --dbg_out_stat                          false
% 1.22/1.03  ------ Parsing...
% 1.22/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.22/1.03  
% 1.22/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.22/1.03  
% 1.22/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.22/1.03  
% 1.22/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.22/1.03  ------ Proving...
% 1.22/1.03  ------ Problem Properties 
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  clauses                                 19
% 1.22/1.03  conjectures                             3
% 1.22/1.03  EPR                                     4
% 1.22/1.03  Horn                                    18
% 1.22/1.03  unary                                   10
% 1.22/1.03  binary                                  4
% 1.22/1.03  lits                                    33
% 1.22/1.03  lits eq                                 13
% 1.22/1.03  fd_pure                                 0
% 1.22/1.03  fd_pseudo                               0
% 1.22/1.03  fd_cond                                 2
% 1.22/1.03  fd_pseudo_cond                          2
% 1.22/1.03  AC symbols                              0
% 1.22/1.03  
% 1.22/1.03  ------ Schedule dynamic 5 is on 
% 1.22/1.03  
% 1.22/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  ------ 
% 1.22/1.03  Current options:
% 1.22/1.03  ------ 
% 1.22/1.03  
% 1.22/1.03  ------ Input Options
% 1.22/1.03  
% 1.22/1.03  --out_options                           all
% 1.22/1.03  --tptp_safe_out                         true
% 1.22/1.03  --problem_path                          ""
% 1.22/1.03  --include_path                          ""
% 1.22/1.03  --clausifier                            res/vclausify_rel
% 1.22/1.03  --clausifier_options                    --mode clausify
% 1.22/1.03  --stdin                                 false
% 1.22/1.03  --stats_out                             all
% 1.22/1.03  
% 1.22/1.03  ------ General Options
% 1.22/1.03  
% 1.22/1.03  --fof                                   false
% 1.22/1.03  --time_out_real                         305.
% 1.22/1.03  --time_out_virtual                      -1.
% 1.22/1.03  --symbol_type_check                     false
% 1.22/1.03  --clausify_out                          false
% 1.22/1.03  --sig_cnt_out                           false
% 1.22/1.03  --trig_cnt_out                          false
% 1.22/1.03  --trig_cnt_out_tolerance                1.
% 1.22/1.03  --trig_cnt_out_sk_spl                   false
% 1.22/1.03  --abstr_cl_out                          false
% 1.22/1.03  
% 1.22/1.03  ------ Global Options
% 1.22/1.03  
% 1.22/1.03  --schedule                              default
% 1.22/1.03  --add_important_lit                     false
% 1.22/1.03  --prop_solver_per_cl                    1000
% 1.22/1.03  --min_unsat_core                        false
% 1.22/1.03  --soft_assumptions                      false
% 1.22/1.03  --soft_lemma_size                       3
% 1.22/1.03  --prop_impl_unit_size                   0
% 1.22/1.03  --prop_impl_unit                        []
% 1.22/1.03  --share_sel_clauses                     true
% 1.22/1.03  --reset_solvers                         false
% 1.22/1.03  --bc_imp_inh                            [conj_cone]
% 1.22/1.03  --conj_cone_tolerance                   3.
% 1.22/1.03  --extra_neg_conj                        none
% 1.22/1.03  --large_theory_mode                     true
% 1.22/1.03  --prolific_symb_bound                   200
% 1.22/1.03  --lt_threshold                          2000
% 1.22/1.03  --clause_weak_htbl                      true
% 1.22/1.03  --gc_record_bc_elim                     false
% 1.22/1.03  
% 1.22/1.03  ------ Preprocessing Options
% 1.22/1.03  
% 1.22/1.03  --preprocessing_flag                    true
% 1.22/1.03  --time_out_prep_mult                    0.1
% 1.22/1.03  --splitting_mode                        input
% 1.22/1.03  --splitting_grd                         true
% 1.22/1.03  --splitting_cvd                         false
% 1.22/1.03  --splitting_cvd_svl                     false
% 1.22/1.03  --splitting_nvd                         32
% 1.22/1.03  --sub_typing                            true
% 1.22/1.03  --prep_gs_sim                           true
% 1.22/1.03  --prep_unflatten                        true
% 1.22/1.03  --prep_res_sim                          true
% 1.22/1.03  --prep_upred                            true
% 1.22/1.03  --prep_sem_filter                       exhaustive
% 1.22/1.03  --prep_sem_filter_out                   false
% 1.22/1.03  --pred_elim                             true
% 1.22/1.03  --res_sim_input                         true
% 1.22/1.03  --eq_ax_congr_red                       true
% 1.22/1.03  --pure_diseq_elim                       true
% 1.22/1.03  --brand_transform                       false
% 1.22/1.03  --non_eq_to_eq                          false
% 1.22/1.03  --prep_def_merge                        true
% 1.22/1.03  --prep_def_merge_prop_impl              false
% 1.22/1.03  --prep_def_merge_mbd                    true
% 1.22/1.03  --prep_def_merge_tr_red                 false
% 1.22/1.03  --prep_def_merge_tr_cl                  false
% 1.22/1.03  --smt_preprocessing                     true
% 1.22/1.03  --smt_ac_axioms                         fast
% 1.22/1.03  --preprocessed_out                      false
% 1.22/1.03  --preprocessed_stats                    false
% 1.22/1.03  
% 1.22/1.03  ------ Abstraction refinement Options
% 1.22/1.03  
% 1.22/1.03  --abstr_ref                             []
% 1.22/1.03  --abstr_ref_prep                        false
% 1.22/1.03  --abstr_ref_until_sat                   false
% 1.22/1.03  --abstr_ref_sig_restrict                funpre
% 1.22/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.22/1.03  --abstr_ref_under                       []
% 1.22/1.03  
% 1.22/1.03  ------ SAT Options
% 1.22/1.03  
% 1.22/1.03  --sat_mode                              false
% 1.22/1.03  --sat_fm_restart_options                ""
% 1.22/1.03  --sat_gr_def                            false
% 1.22/1.03  --sat_epr_types                         true
% 1.22/1.03  --sat_non_cyclic_types                  false
% 1.22/1.03  --sat_finite_models                     false
% 1.22/1.03  --sat_fm_lemmas                         false
% 1.22/1.03  --sat_fm_prep                           false
% 1.22/1.03  --sat_fm_uc_incr                        true
% 1.22/1.03  --sat_out_model                         small
% 1.22/1.03  --sat_out_clauses                       false
% 1.22/1.03  
% 1.22/1.03  ------ QBF Options
% 1.22/1.03  
% 1.22/1.03  --qbf_mode                              false
% 1.22/1.03  --qbf_elim_univ                         false
% 1.22/1.03  --qbf_dom_inst                          none
% 1.22/1.03  --qbf_dom_pre_inst                      false
% 1.22/1.03  --qbf_sk_in                             false
% 1.22/1.03  --qbf_pred_elim                         true
% 1.22/1.03  --qbf_split                             512
% 1.22/1.03  
% 1.22/1.03  ------ BMC1 Options
% 1.22/1.03  
% 1.22/1.03  --bmc1_incremental                      false
% 1.22/1.03  --bmc1_axioms                           reachable_all
% 1.22/1.03  --bmc1_min_bound                        0
% 1.22/1.03  --bmc1_max_bound                        -1
% 1.22/1.03  --bmc1_max_bound_default                -1
% 1.22/1.03  --bmc1_symbol_reachability              true
% 1.22/1.03  --bmc1_property_lemmas                  false
% 1.22/1.03  --bmc1_k_induction                      false
% 1.22/1.03  --bmc1_non_equiv_states                 false
% 1.22/1.03  --bmc1_deadlock                         false
% 1.22/1.03  --bmc1_ucm                              false
% 1.22/1.03  --bmc1_add_unsat_core                   none
% 1.22/1.03  --bmc1_unsat_core_children              false
% 1.22/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.22/1.03  --bmc1_out_stat                         full
% 1.22/1.03  --bmc1_ground_init                      false
% 1.22/1.03  --bmc1_pre_inst_next_state              false
% 1.22/1.03  --bmc1_pre_inst_state                   false
% 1.22/1.03  --bmc1_pre_inst_reach_state             false
% 1.22/1.03  --bmc1_out_unsat_core                   false
% 1.22/1.03  --bmc1_aig_witness_out                  false
% 1.22/1.03  --bmc1_verbose                          false
% 1.22/1.03  --bmc1_dump_clauses_tptp                false
% 1.22/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.22/1.03  --bmc1_dump_file                        -
% 1.22/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.22/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.22/1.03  --bmc1_ucm_extend_mode                  1
% 1.22/1.03  --bmc1_ucm_init_mode                    2
% 1.22/1.03  --bmc1_ucm_cone_mode                    none
% 1.22/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.22/1.03  --bmc1_ucm_relax_model                  4
% 1.22/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.22/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.22/1.03  --bmc1_ucm_layered_model                none
% 1.22/1.03  --bmc1_ucm_max_lemma_size               10
% 1.22/1.03  
% 1.22/1.03  ------ AIG Options
% 1.22/1.03  
% 1.22/1.03  --aig_mode                              false
% 1.22/1.03  
% 1.22/1.03  ------ Instantiation Options
% 1.22/1.03  
% 1.22/1.03  --instantiation_flag                    true
% 1.22/1.03  --inst_sos_flag                         false
% 1.22/1.03  --inst_sos_phase                        true
% 1.22/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.22/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.22/1.03  --inst_lit_sel_side                     none
% 1.22/1.03  --inst_solver_per_active                1400
% 1.22/1.03  --inst_solver_calls_frac                1.
% 1.22/1.03  --inst_passive_queue_type               priority_queues
% 1.22/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.22/1.03  --inst_passive_queues_freq              [25;2]
% 1.22/1.03  --inst_dismatching                      true
% 1.22/1.03  --inst_eager_unprocessed_to_passive     true
% 1.22/1.03  --inst_prop_sim_given                   true
% 1.22/1.03  --inst_prop_sim_new                     false
% 1.22/1.03  --inst_subs_new                         false
% 1.22/1.03  --inst_eq_res_simp                      false
% 1.22/1.03  --inst_subs_given                       false
% 1.22/1.03  --inst_orphan_elimination               true
% 1.22/1.03  --inst_learning_loop_flag               true
% 1.22/1.03  --inst_learning_start                   3000
% 1.22/1.03  --inst_learning_factor                  2
% 1.22/1.03  --inst_start_prop_sim_after_learn       3
% 1.22/1.03  --inst_sel_renew                        solver
% 1.22/1.03  --inst_lit_activity_flag                true
% 1.22/1.03  --inst_restr_to_given                   false
% 1.22/1.03  --inst_activity_threshold               500
% 1.22/1.03  --inst_out_proof                        true
% 1.22/1.03  
% 1.22/1.03  ------ Resolution Options
% 1.22/1.03  
% 1.22/1.03  --resolution_flag                       false
% 1.22/1.03  --res_lit_sel                           adaptive
% 1.22/1.03  --res_lit_sel_side                      none
% 1.22/1.03  --res_ordering                          kbo
% 1.22/1.03  --res_to_prop_solver                    active
% 1.22/1.03  --res_prop_simpl_new                    false
% 1.22/1.03  --res_prop_simpl_given                  true
% 1.22/1.03  --res_passive_queue_type                priority_queues
% 1.22/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.22/1.03  --res_passive_queues_freq               [15;5]
% 1.22/1.03  --res_forward_subs                      full
% 1.22/1.03  --res_backward_subs                     full
% 1.22/1.03  --res_forward_subs_resolution           true
% 1.22/1.03  --res_backward_subs_resolution          true
% 1.22/1.03  --res_orphan_elimination                true
% 1.22/1.03  --res_time_limit                        2.
% 1.22/1.03  --res_out_proof                         true
% 1.22/1.03  
% 1.22/1.03  ------ Superposition Options
% 1.22/1.03  
% 1.22/1.03  --superposition_flag                    true
% 1.22/1.03  --sup_passive_queue_type                priority_queues
% 1.22/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.22/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.22/1.03  --demod_completeness_check              fast
% 1.22/1.03  --demod_use_ground                      true
% 1.22/1.03  --sup_to_prop_solver                    passive
% 1.22/1.03  --sup_prop_simpl_new                    true
% 1.22/1.03  --sup_prop_simpl_given                  true
% 1.22/1.03  --sup_fun_splitting                     false
% 1.22/1.03  --sup_smt_interval                      50000
% 1.22/1.03  
% 1.22/1.03  ------ Superposition Simplification Setup
% 1.22/1.03  
% 1.22/1.03  --sup_indices_passive                   []
% 1.22/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.22/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_full_bw                           [BwDemod]
% 1.22/1.03  --sup_immed_triv                        [TrivRules]
% 1.22/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.22/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_immed_bw_main                     []
% 1.22/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.22/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.03  
% 1.22/1.03  ------ Combination Options
% 1.22/1.03  
% 1.22/1.03  --comb_res_mult                         3
% 1.22/1.03  --comb_sup_mult                         2
% 1.22/1.03  --comb_inst_mult                        10
% 1.22/1.03  
% 1.22/1.03  ------ Debug Options
% 1.22/1.03  
% 1.22/1.03  --dbg_backtrace                         false
% 1.22/1.03  --dbg_dump_prop_clauses                 false
% 1.22/1.03  --dbg_dump_prop_clauses_file            -
% 1.22/1.03  --dbg_out_stat                          false
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  ------ Proving...
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  % SZS status Theorem for theBenchmark.p
% 1.22/1.03  
% 1.22/1.03   Resolution empty clause
% 1.22/1.03  
% 1.22/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.22/1.03  
% 1.22/1.03  fof(f10,axiom,(
% 1.22/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f53,plain,(
% 1.22/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.22/1.03    inference(cnf_transformation,[],[f10])).
% 1.22/1.03  
% 1.22/1.03  fof(f9,axiom,(
% 1.22/1.03    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f22,plain,(
% 1.22/1.03    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.22/1.03    inference(ennf_transformation,[],[f9])).
% 1.22/1.03  
% 1.22/1.03  fof(f51,plain,(
% 1.22/1.03    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f22])).
% 1.22/1.03  
% 1.22/1.03  fof(f13,axiom,(
% 1.22/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f27,plain,(
% 1.22/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/1.03    inference(ennf_transformation,[],[f13])).
% 1.22/1.03  
% 1.22/1.03  fof(f57,plain,(
% 1.22/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f27])).
% 1.22/1.03  
% 1.22/1.03  fof(f6,axiom,(
% 1.22/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f48,plain,(
% 1.22/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f6])).
% 1.22/1.03  
% 1.22/1.03  fof(f2,axiom,(
% 1.22/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f42,plain,(
% 1.22/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f2])).
% 1.22/1.03  
% 1.22/1.03  fof(f1,axiom,(
% 1.22/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f32,plain,(
% 1.22/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/1.03    inference(nnf_transformation,[],[f1])).
% 1.22/1.03  
% 1.22/1.03  fof(f33,plain,(
% 1.22/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/1.03    inference(flattening,[],[f32])).
% 1.22/1.03  
% 1.22/1.03  fof(f41,plain,(
% 1.22/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f33])).
% 1.22/1.03  
% 1.22/1.03  fof(f16,conjecture,(
% 1.22/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f17,negated_conjecture,(
% 1.22/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.22/1.03    inference(negated_conjecture,[],[f16])).
% 1.22/1.03  
% 1.22/1.03  fof(f18,plain,(
% 1.22/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.22/1.03    inference(pure_predicate_removal,[],[f17])).
% 1.22/1.03  
% 1.22/1.03  fof(f30,plain,(
% 1.22/1.03    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.22/1.03    inference(ennf_transformation,[],[f18])).
% 1.22/1.03  
% 1.22/1.03  fof(f31,plain,(
% 1.22/1.03    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.22/1.03    inference(flattening,[],[f30])).
% 1.22/1.03  
% 1.22/1.03  fof(f37,plain,(
% 1.22/1.03    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.22/1.03    introduced(choice_axiom,[])).
% 1.22/1.03  
% 1.22/1.03  fof(f38,plain,(
% 1.22/1.03    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.22/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f37])).
% 1.22/1.03  
% 1.22/1.03  fof(f61,plain,(
% 1.22/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.22/1.03    inference(cnf_transformation,[],[f38])).
% 1.22/1.03  
% 1.22/1.03  fof(f3,axiom,(
% 1.22/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f43,plain,(
% 1.22/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f3])).
% 1.22/1.03  
% 1.22/1.03  fof(f4,axiom,(
% 1.22/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f44,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f4])).
% 1.22/1.03  
% 1.22/1.03  fof(f64,plain,(
% 1.22/1.03    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.22/1.03    inference(definition_unfolding,[],[f43,f44])).
% 1.22/1.03  
% 1.22/1.03  fof(f70,plain,(
% 1.22/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 1.22/1.03    inference(definition_unfolding,[],[f61,f64])).
% 1.22/1.03  
% 1.22/1.03  fof(f14,axiom,(
% 1.22/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f19,plain,(
% 1.22/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.22/1.03    inference(pure_predicate_removal,[],[f14])).
% 1.22/1.03  
% 1.22/1.03  fof(f28,plain,(
% 1.22/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/1.03    inference(ennf_transformation,[],[f19])).
% 1.22/1.03  
% 1.22/1.03  fof(f58,plain,(
% 1.22/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f28])).
% 1.22/1.03  
% 1.22/1.03  fof(f8,axiom,(
% 1.22/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f21,plain,(
% 1.22/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.22/1.03    inference(ennf_transformation,[],[f8])).
% 1.22/1.03  
% 1.22/1.03  fof(f36,plain,(
% 1.22/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.22/1.03    inference(nnf_transformation,[],[f21])).
% 1.22/1.03  
% 1.22/1.03  fof(f49,plain,(
% 1.22/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f36])).
% 1.22/1.03  
% 1.22/1.03  fof(f5,axiom,(
% 1.22/1.03    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f34,plain,(
% 1.22/1.03    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.22/1.03    inference(nnf_transformation,[],[f5])).
% 1.22/1.03  
% 1.22/1.03  fof(f35,plain,(
% 1.22/1.03    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.22/1.03    inference(flattening,[],[f34])).
% 1.22/1.03  
% 1.22/1.03  fof(f45,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f35])).
% 1.22/1.03  
% 1.22/1.03  fof(f67,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 1.22/1.03    inference(definition_unfolding,[],[f45,f64,f64])).
% 1.22/1.03  
% 1.22/1.03  fof(f63,plain,(
% 1.22/1.03    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.22/1.03    inference(cnf_transformation,[],[f38])).
% 1.22/1.03  
% 1.22/1.03  fof(f69,plain,(
% 1.22/1.03    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.22/1.03    inference(definition_unfolding,[],[f63,f64,f64])).
% 1.22/1.03  
% 1.22/1.03  fof(f15,axiom,(
% 1.22/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f29,plain,(
% 1.22/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/1.03    inference(ennf_transformation,[],[f15])).
% 1.22/1.03  
% 1.22/1.03  fof(f59,plain,(
% 1.22/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f29])).
% 1.22/1.03  
% 1.22/1.03  fof(f12,axiom,(
% 1.22/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f25,plain,(
% 1.22/1.03    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.22/1.03    inference(ennf_transformation,[],[f12])).
% 1.22/1.03  
% 1.22/1.03  fof(f26,plain,(
% 1.22/1.03    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.22/1.03    inference(flattening,[],[f25])).
% 1.22/1.03  
% 1.22/1.03  fof(f56,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f26])).
% 1.22/1.03  
% 1.22/1.03  fof(f68,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_enumset1(X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.22/1.03    inference(definition_unfolding,[],[f56,f64,f64])).
% 1.22/1.03  
% 1.22/1.03  fof(f60,plain,(
% 1.22/1.03    v1_funct_1(sK3)),
% 1.22/1.03    inference(cnf_transformation,[],[f38])).
% 1.22/1.03  
% 1.22/1.03  fof(f11,axiom,(
% 1.22/1.03    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f23,plain,(
% 1.22/1.03    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.22/1.03    inference(ennf_transformation,[],[f11])).
% 1.22/1.03  
% 1.22/1.03  fof(f24,plain,(
% 1.22/1.03    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.22/1.03    inference(flattening,[],[f23])).
% 1.22/1.03  
% 1.22/1.03  fof(f54,plain,(
% 1.22/1.03    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f24])).
% 1.22/1.03  
% 1.22/1.03  cnf(c_11,plain,
% 1.22/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.22/1.03      inference(cnf_transformation,[],[f53]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_10,plain,
% 1.22/1.03      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1023,plain,
% 1.22/1.03      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 1.22/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1447,plain,
% 1.22/1.03      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 1.22/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_11,c_1023]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_16,plain,
% 1.22/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1135,plain,
% 1.22/1.03      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.22/1.03      | v1_relat_1(k1_xboole_0) ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1137,plain,
% 1.22/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.22/1.03      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1135]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_7,plain,
% 1.22/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.22/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1136,plain,
% 1.22/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1139,plain,
% 1.22/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1543,plain,
% 1.22/1.03      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 1.22/1.03      inference(global_propositional_subsumption,
% 1.22/1.03                [status(thm)],
% 1.22/1.03                [c_1447,c_1137,c_1139]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3,plain,
% 1.22/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f42]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1028,plain,
% 1.22/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_0,plain,
% 1.22/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.22/1.03      inference(cnf_transformation,[],[f41]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1030,plain,
% 1.22/1.03      ( X0 = X1
% 1.22/1.03      | r1_tarski(X0,X1) != iProver_top
% 1.22/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1744,plain,
% 1.22/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1028,c_1030]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2038,plain,
% 1.22/1.03      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1543,c_1744]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_21,negated_conjecture,
% 1.22/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
% 1.22/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1017,plain,
% 1.22/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_17,plain,
% 1.22/1.03      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.22/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_9,plain,
% 1.22/1.03      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f49]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_323,plain,
% 1.22/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.22/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 1.22/1.03      | ~ v1_relat_1(X0) ),
% 1.22/1.03      inference(resolution,[status(thm)],[c_17,c_9]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_327,plain,
% 1.22/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 1.22/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.22/1.03      inference(global_propositional_subsumption,[status(thm)],[c_323,c_16]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_328,plain,
% 1.22/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.22/1.03      | r1_tarski(k1_relat_1(X0),X1) ),
% 1.22/1.03      inference(renaming,[status(thm)],[c_327]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1015,plain,
% 1.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.22/1.03      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1325,plain,
% 1.22/1.03      ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1017,c_1015]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_6,plain,
% 1.22/1.03      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
% 1.22/1.03      | k1_enumset1(X1,X1,X1) = X0
% 1.22/1.03      | k1_xboole_0 = X0 ),
% 1.22/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1025,plain,
% 1.22/1.03      ( k1_enumset1(X0,X0,X0) = X1
% 1.22/1.03      | k1_xboole_0 = X1
% 1.22/1.03      | r1_tarski(X1,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1917,plain,
% 1.22/1.03      ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
% 1.22/1.03      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1325,c_1025]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_19,negated_conjecture,
% 1.22/1.03      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 1.22/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1018,plain,
% 1.22/1.03      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2131,plain,
% 1.22/1.03      ( k1_relat_1(sK3) = k1_xboole_0
% 1.22/1.03      | r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1917,c_1018]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1143,plain,
% 1.22/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 1.22/1.03      | v1_relat_1(sK3) ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_18,plain,
% 1.22/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.22/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.22/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1181,plain,
% 1.22/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 1.22/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1225,plain,
% 1.22/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 1.22/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_1181]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1380,plain,
% 1.22/1.03      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_722,plain,
% 1.22/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.22/1.03      theory(equality) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1164,plain,
% 1.22/1.03      ( ~ r1_tarski(X0,X1)
% 1.22/1.03      | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 1.22/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 1.22/1.03      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_722]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1224,plain,
% 1.22/1.03      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 1.22/1.03      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 1.22/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 1.22/1.03      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_1164]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1381,plain,
% 1.22/1.03      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 1.22/1.03      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 1.22/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 1.22/1.03      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_1224]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_15,plain,
% 1.22/1.03      ( ~ v1_funct_1(X0)
% 1.22/1.03      | ~ v1_relat_1(X0)
% 1.22/1.03      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 1.22/1.03      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_22,negated_conjecture,
% 1.22/1.03      ( v1_funct_1(sK3) ),
% 1.22/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_226,plain,
% 1.22/1.03      ( ~ v1_relat_1(X0)
% 1.22/1.03      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 1.22/1.03      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 1.22/1.03      | sK3 != X0 ),
% 1.22/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_227,plain,
% 1.22/1.03      ( ~ v1_relat_1(sK3)
% 1.22/1.03      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 1.22/1.03      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 1.22/1.03      inference(unflattening,[status(thm)],[c_226]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1016,plain,
% 1.22/1.03      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 1.22/1.03      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 1.22/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_24,plain,
% 1.22/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_228,plain,
% 1.22/1.03      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 1.22/1.03      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 1.22/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1144,plain,
% 1.22/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
% 1.22/1.03      | v1_relat_1(sK3) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1143]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1157,plain,
% 1.22/1.03      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 1.22/1.03      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3) ),
% 1.22/1.03      inference(global_propositional_subsumption,
% 1.22/1.03                [status(thm)],
% 1.22/1.03                [c_1016,c_24,c_228,c_1144]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1158,plain,
% 1.22/1.03      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 1.22/1.03      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 1.22/1.03      inference(renaming,[status(thm)],[c_1157]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2128,plain,
% 1.22/1.03      ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 1.22/1.03      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1917,c_1158]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2315,plain,
% 1.22/1.03      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.22/1.03      inference(global_propositional_subsumption,
% 1.22/1.03                [status(thm)],
% 1.22/1.03                [c_2131,c_21,c_19,c_1143,c_1225,c_1380,c_1381,c_2128]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_14,plain,
% 1.22/1.03      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 1.22/1.03      inference(cnf_transformation,[],[f54]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1021,plain,
% 1.22/1.03      ( k1_relat_1(X0) != k1_xboole_0
% 1.22/1.03      | k1_xboole_0 = X0
% 1.22/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2333,plain,
% 1.22/1.03      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_2315,c_1021]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1243,plain,
% 1.22/1.03      ( ~ v1_relat_1(sK3)
% 1.22/1.03      | k1_relat_1(sK3) != k1_xboole_0
% 1.22/1.03      | k1_xboole_0 = sK3 ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_720,plain,( X0 = X0 ),theory(equality) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1256,plain,
% 1.22/1.03      ( sK3 = sK3 ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_720]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_721,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1457,plain,
% 1.22/1.03      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_721]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2070,plain,
% 1.22/1.03      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_1457]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2071,plain,
% 1.22/1.03      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_2070]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2404,plain,
% 1.22/1.03      ( sK3 = k1_xboole_0 ),
% 1.22/1.03      inference(global_propositional_subsumption,
% 1.22/1.03                [status(thm)],
% 1.22/1.03                [c_2333,c_21,c_19,c_1143,c_1225,c_1243,c_1256,c_1380,c_1381,
% 1.22/1.03                 c_2071,c_2128]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1019,plain,
% 1.22/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.22/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1926,plain,
% 1.22/1.03      ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1017,c_1019]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2159,plain,
% 1.22/1.03      ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_1926,c_1018]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2408,plain,
% 1.22/1.03      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_2404,c_2159]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2615,plain,
% 1.22/1.03      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_2038,c_2408]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2777,plain,
% 1.22/1.03      ( $false ),
% 1.22/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_2615,c_1028]) ).
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.22/1.03  
% 1.22/1.03  ------                               Statistics
% 1.22/1.03  
% 1.22/1.03  ------ General
% 1.22/1.03  
% 1.22/1.03  abstr_ref_over_cycles:                  0
% 1.22/1.03  abstr_ref_under_cycles:                 0
% 1.22/1.03  gc_basic_clause_elim:                   0
% 1.22/1.03  forced_gc_time:                         0
% 1.22/1.03  parsing_time:                           0.021
% 1.22/1.03  unif_index_cands_time:                  0.
% 1.22/1.03  unif_index_add_time:                    0.
% 1.22/1.03  orderings_time:                         0.
% 1.22/1.03  out_proof_time:                         0.009
% 1.22/1.03  total_time:                             0.114
% 1.22/1.03  num_of_symbols:                         49
% 1.22/1.03  num_of_terms:                           2070
% 1.22/1.03  
% 1.22/1.03  ------ Preprocessing
% 1.22/1.03  
% 1.22/1.03  num_of_splits:                          0
% 1.22/1.03  num_of_split_atoms:                     0
% 1.22/1.03  num_of_reused_defs:                     0
% 1.22/1.03  num_eq_ax_congr_red:                    9
% 1.22/1.03  num_of_sem_filtered_clauses:            1
% 1.22/1.03  num_of_subtypes:                        0
% 1.22/1.03  monotx_restored_types:                  0
% 1.22/1.03  sat_num_of_epr_types:                   0
% 1.22/1.03  sat_num_of_non_cyclic_types:            0
% 1.22/1.03  sat_guarded_non_collapsed_types:        0
% 1.22/1.03  num_pure_diseq_elim:                    0
% 1.22/1.03  simp_replaced_by:                       0
% 1.22/1.03  res_preprocessed:                       104
% 1.22/1.03  prep_upred:                             0
% 1.22/1.03  prep_unflattend:                        21
% 1.22/1.03  smt_new_axioms:                         0
% 1.22/1.03  pred_elim_cands:                        3
% 1.22/1.03  pred_elim:                              2
% 1.22/1.03  pred_elim_cl:                           3
% 1.22/1.03  pred_elim_cycles:                       7
% 1.22/1.03  merged_defs:                            0
% 1.22/1.03  merged_defs_ncl:                        0
% 1.22/1.03  bin_hyper_res:                          0
% 1.22/1.03  prep_cycles:                            4
% 1.22/1.03  pred_elim_time:                         0.004
% 1.22/1.03  splitting_time:                         0.
% 1.22/1.03  sem_filter_time:                        0.
% 1.22/1.03  monotx_time:                            0.
% 1.22/1.03  subtype_inf_time:                       0.
% 1.22/1.03  
% 1.22/1.03  ------ Problem properties
% 1.22/1.03  
% 1.22/1.03  clauses:                                19
% 1.22/1.03  conjectures:                            3
% 1.22/1.03  epr:                                    4
% 1.22/1.03  horn:                                   18
% 1.22/1.03  ground:                                 5
% 1.22/1.03  unary:                                  10
% 1.22/1.03  binary:                                 4
% 1.22/1.03  lits:                                   33
% 1.22/1.03  lits_eq:                                13
% 1.22/1.03  fd_pure:                                0
% 1.22/1.03  fd_pseudo:                              0
% 1.22/1.03  fd_cond:                                2
% 1.22/1.03  fd_pseudo_cond:                         2
% 1.22/1.03  ac_symbols:                             0
% 1.22/1.03  
% 1.22/1.03  ------ Propositional Solver
% 1.22/1.03  
% 1.22/1.03  prop_solver_calls:                      27
% 1.22/1.03  prop_fast_solver_calls:                 571
% 1.22/1.03  smt_solver_calls:                       0
% 1.22/1.03  smt_fast_solver_calls:                  0
% 1.22/1.03  prop_num_of_clauses:                    984
% 1.22/1.03  prop_preprocess_simplified:             3966
% 1.22/1.03  prop_fo_subsumed:                       10
% 1.22/1.03  prop_solver_time:                       0.
% 1.22/1.03  smt_solver_time:                        0.
% 1.22/1.03  smt_fast_solver_time:                   0.
% 1.22/1.03  prop_fast_solver_time:                  0.
% 1.22/1.03  prop_unsat_core_time:                   0.
% 1.22/1.03  
% 1.22/1.03  ------ QBF
% 1.22/1.03  
% 1.22/1.03  qbf_q_res:                              0
% 1.22/1.03  qbf_num_tautologies:                    0
% 1.22/1.03  qbf_prep_cycles:                        0
% 1.22/1.03  
% 1.22/1.03  ------ BMC1
% 1.22/1.03  
% 1.22/1.03  bmc1_current_bound:                     -1
% 1.22/1.03  bmc1_last_solved_bound:                 -1
% 1.22/1.03  bmc1_unsat_core_size:                   -1
% 1.22/1.03  bmc1_unsat_core_parents_size:           -1
% 1.22/1.03  bmc1_merge_next_fun:                    0
% 1.22/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.22/1.03  
% 1.22/1.03  ------ Instantiation
% 1.22/1.03  
% 1.22/1.03  inst_num_of_clauses:                    337
% 1.22/1.03  inst_num_in_passive:                    128
% 1.22/1.03  inst_num_in_active:                     154
% 1.22/1.03  inst_num_in_unprocessed:                55
% 1.22/1.03  inst_num_of_loops:                      180
% 1.22/1.03  inst_num_of_learning_restarts:          0
% 1.22/1.03  inst_num_moves_active_passive:          24
% 1.22/1.03  inst_lit_activity:                      0
% 1.22/1.03  inst_lit_activity_moves:                0
% 1.22/1.03  inst_num_tautologies:                   0
% 1.22/1.03  inst_num_prop_implied:                  0
% 1.22/1.03  inst_num_existing_simplified:           0
% 1.22/1.03  inst_num_eq_res_simplified:             0
% 1.22/1.03  inst_num_child_elim:                    0
% 1.22/1.03  inst_num_of_dismatching_blockings:      38
% 1.22/1.03  inst_num_of_non_proper_insts:           246
% 1.22/1.03  inst_num_of_duplicates:                 0
% 1.22/1.03  inst_inst_num_from_inst_to_res:         0
% 1.22/1.03  inst_dismatching_checking_time:         0.
% 1.22/1.03  
% 1.22/1.03  ------ Resolution
% 1.22/1.03  
% 1.22/1.03  res_num_of_clauses:                     0
% 1.22/1.03  res_num_in_passive:                     0
% 1.22/1.03  res_num_in_active:                      0
% 1.22/1.03  res_num_of_loops:                       108
% 1.22/1.03  res_forward_subset_subsumed:            37
% 1.22/1.03  res_backward_subset_subsumed:           0
% 1.22/1.03  res_forward_subsumed:                   0
% 1.22/1.03  res_backward_subsumed:                  0
% 1.22/1.03  res_forward_subsumption_resolution:     0
% 1.22/1.03  res_backward_subsumption_resolution:    0
% 1.22/1.03  res_clause_to_clause_subsumption:       102
% 1.22/1.03  res_orphan_elimination:                 0
% 1.22/1.03  res_tautology_del:                      13
% 1.22/1.03  res_num_eq_res_simplified:              0
% 1.22/1.03  res_num_sel_changes:                    0
% 1.22/1.03  res_moves_from_active_to_pass:          0
% 1.22/1.03  
% 1.22/1.03  ------ Superposition
% 1.22/1.03  
% 1.22/1.03  sup_time_total:                         0.
% 1.22/1.03  sup_time_generating:                    0.
% 1.22/1.03  sup_time_sim_full:                      0.
% 1.22/1.03  sup_time_sim_immed:                     0.
% 1.22/1.03  
% 1.22/1.03  sup_num_of_clauses:                     24
% 1.22/1.03  sup_num_in_active:                      22
% 1.22/1.03  sup_num_in_passive:                     2
% 1.22/1.03  sup_num_of_loops:                       35
% 1.22/1.03  sup_fw_superposition:                   21
% 1.22/1.03  sup_bw_superposition:                   10
% 1.22/1.03  sup_immediate_simplified:               11
% 1.22/1.03  sup_given_eliminated:                   0
% 1.22/1.03  comparisons_done:                       0
% 1.22/1.03  comparisons_avoided:                    0
% 1.22/1.03  
% 1.22/1.03  ------ Simplifications
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  sim_fw_subset_subsumed:                 2
% 1.22/1.03  sim_bw_subset_subsumed:                 2
% 1.22/1.03  sim_fw_subsumed:                        8
% 1.22/1.03  sim_bw_subsumed:                        0
% 1.22/1.03  sim_fw_subsumption_res:                 1
% 1.22/1.03  sim_bw_subsumption_res:                 0
% 1.22/1.03  sim_tautology_del:                      0
% 1.22/1.03  sim_eq_tautology_del:                   7
% 1.22/1.03  sim_eq_res_simp:                        0
% 1.22/1.03  sim_fw_demodulated:                     0
% 1.22/1.03  sim_bw_demodulated:                     13
% 1.22/1.03  sim_light_normalised:                   5
% 1.22/1.03  sim_joinable_taut:                      0
% 1.22/1.03  sim_joinable_simp:                      0
% 1.22/1.03  sim_ac_normalised:                      0
% 1.22/1.03  sim_smt_subsumption:                    0
% 1.22/1.03  
%------------------------------------------------------------------------------
